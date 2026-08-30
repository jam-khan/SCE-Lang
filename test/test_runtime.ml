(* Host capabilities and runtime linking, interpreted and through wasm.

   Effects are captured by redirecting Units.Host.out, so every test also
   checks the *trace* — which lines were printed, in which order — not just
   the final value. The fixtures are the shipped case studies under examples/. *)

let failures = ref 0

let check name condition =
  if condition then Printf.printf "PASS  %s\n" name
  else (
    Printf.printf "FAIL  %s\n" name;
    incr failures)

let contains hay needle =
  let nh = String.length hay and nn = String.length needle in
  let rec go i = i + nn <= nh && (String.sub hay i nn = needle || go (i + 1)) in
  nn = 0 || go 0

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let write_file path contents =
  let oc = open_out_bin path in
  output_string oc contents;
  close_out oc

let temp_dir () =
  let d = Filename.temp_file "runtime" "" in
  Sys.remove d;
  Sys.mkdir d 0o755;
  d

(* Compile a unit source file living in `dir` (interfaces resolve there). *)
let compile dir name =
  let path = Filename.concat dir name in
  match Sce.Pipeline.compile_unit ~path (read_file path) with
  | Ok (art, sceis) ->
    List.iter (fun (n, c) -> write_file (Filename.concat dir n) c) sceis;
    Ok art
  | Error e -> Error e

let compile_exn dir name =
  match compile dir name with
  | Ok a -> a
  | Error e -> failwith (name ^ ": " ^ e.stage ^ ": " ^ e.message)

let link_exn arts =
  match Sce.Pipeline.link_artifacts arts with
  | Ok a -> a
  | Error e -> failwith e.message

(* Evaluate with cwd = dir (runtime loads resolve there) and the print
   capability captured; returns (type, value, trace lines). *)
let run_traced dir art =
  let buf = Buffer.create 256 in
  let saved_out = !Units.Host.out in
  let saved_cwd = Sys.getcwd () in
  Units.Host.out := Buffer.add_string buf;
  Sys.chdir dir;
  let finish () =
    Units.Host.out := saved_out;
    Sys.chdir saved_cwd
  in
  match Sce.Pipeline.run_artifact art with
  | Ok (t, v) ->
    finish ();
    let trace =
      String.split_on_char '\n' (String.trim (Buffer.contents buf))
      |> List.filter (fun l -> l <> "")
    in
    (t, v, trace)
  | Error e ->
    finish ();
    failwith (e.stage ^ ": " ^ e.message)

(* Only the sources are copied: every .scei is regenerated in the fixture. *)
let fixture set =
  let src = Filename.concat "../examples" set in
  let dir = temp_dir () in
  Array.iter
    (fun f ->
      if Filename.check_suffix f ".sce" then
        write_file (Filename.concat dir f) (read_file (Filename.concat src f)))
    (Sys.readdir src);
  dir

let sys = Units.Host.sys

(* ---------------- effects through linking ---------------- *)

let () =
  print_endline "-- effects --";
  let dir = fixture "effects" in
  let app = compile_exn dir "app.sce" in
  let t, v, trace = run_traced dir (link_exn [ sys; app ]) in
  check "sys-linked program runs"
    (t = "String" && v = {|"hello, world / hello, again"|});
  check "effect trace is in evaluation order"
    (trace = [ "[app] greeting world"; "[app] greeting again" ])

(* Left-to-right operand order of ^ — a regression test for the interpreter's
   OCaml-inherited right-to-left argument evaluation. *)
let () =
  let dir = temp_dir () in
  write_file (Filename.concat dir "order.sce")
    "import Sys\n\
     let left (u : Top) : String = let l : Top = Sys.print \"L\" in \"l\"\n\
     let right (u : Top) : String = let r : Top = Sys.print \"R\" in \"r\"\n\
     let main : String = left () ^ right ()\n";
  let art = compile_exn dir "order.sce" in
  let _, v, trace = run_traced dir (link_exn [ sys; art ]) in
  check "binop operands evaluate left to right"
    (v = {|"lr"|} && trace = [ "L"; "R" ])

(* Each operand of an in-language link evaluates exactly once. *)
let () =
  let dir = temp_dir () in
  write_file (Filename.concat dir "once.sce")
    "import Sys\n\
     module Once = linkall struct\n\
    \  let boot : Top = Sys.print \"eval\"\n\
    \  let v : Int = 20\n\
     end with functor (X : { boot : Top } & { v : Int }) -> struct\n\
    \  let w : Int = X.v + 1\n\
     end\n\
     let main : Int = Once.w\n";
  let art = compile_exn dir "once.sce" in
  let _, v, trace = run_traced dir (link_exn [ sys; art ]) in
  check "linkall evaluates its provider exactly once"
    (v = "21" && trace = [ "eval" ])

(* The toolchain-level counterpart: a provider unit with a construction-time
   effect, wired into a consumer with two imports. The linker binds each unit
   once, so the boot line appears once — a spliced composition term would
   print it once per wired import, plus once. *)
let () =
  print_endline "\n-- boot --";
  let dir = fixture "boot" in
  let provider = compile_exn dir "provider.sce" in
  let consumer = compile_exn dir "consumer.sce" in
  let _, v, trace = run_traced dir (link_exn [ sys; provider; consumer ]) in
  check "a construction effect fires once across two wired imports"
    (v = "3" && trace = [ "loading provider" ])

(* ---------------- the plugin manager ---------------- *)

let () =
  print_endline "\n-- plugins --";
  let dir = fixture "plugins" in
  let shout = compile_exn dir "shout.sce" in
  let quiet = compile_exn dir "quiet.sce" in
  let manager = compile_exn dir "manager.sce" in
  (match compile dir "evil.sce" with
   | Error e ->
     check "a plugin reaching for Sys is a scope error"
       (e.stage = "desugar" && contains e.message "Sys")
   | Ok _ -> check "a plugin reaching for Sys is a scope error" false);
  (* plugins are loaded at run time from their artifacts *)
  Units.Artifact.save (Filename.concat dir "shout.sceo") shout;
  Units.Artifact.save (Filename.concat dir "quiet.sceo") quiet;
  let prog = link_exn [ sys; Units.Host.loader [ manager ]; manager ] in
  (* the linked program survives a disk round-trip, loader and all *)
  Units.Artifact.save (Filename.concat dir "prog.sceo") prog;
  let prog = Units.Artifact.load (Filename.concat dir "prog.sceo") in
  let _, v, trace = run_traced dir prog in
  check "plugins run under attenuated capabilities"
    (contains v "shout! (quiet) <");
  check "a missing plugin is a value, not a crash"
    (contains v "ghost.sceo");
  check "plugin effects carry their per-plugin prefix, in order"
    (trace = [ "[shout] making some noise"; "[quiet] staying quiet" ])

(* ---------------- two versions of one module ---------------- *)

let () =
  print_endline "\n-- versions --";
  let dir = fixture "versions" in
  let v1 = compile_exn dir "libv1.sce" in
  let v2 = compile_exn dir "libv2.sce" in
  let client = compile_exn dir "client.sce" in
  (match Sce.Pipeline.link_artifacts [ v1; v2; client ] with
   | Error e ->
     check "linking both versions statically is an ambiguity error"
       (contains e.message "both export 'Lib'")
   | Ok _ ->
     check "linking both versions statically is an ambiguity error" false);
  Units.Artifact.save (Filename.concat dir "libv2.sceo") v2;
  let prog = link_exn [ v1; Units.Host.loader [ client ]; client ] in
  let _, v, _ = run_traced dir prog in
  check "static v1 and loaded v2 coexist, chosen per use site"
    (v = {|"hello, world (v1) | HELLO, world (v2)"|})

(* ---------------- dynamic upgrade with state handoff ---------------- *)

let () =
  print_endline "\n-- upgrade --";
  let dir = fixture "upgrade" in
  let v1 = compile_exn dir "appv1.sce" in
  let v2 = compile_exn dir "appv2.sce" in
  let driver = compile_exn dir "driver.sce" in
  Units.Artifact.save (Filename.concat dir "appv2.sceo") v2;
  let prog = link_exn [ v1; Units.Host.loader [ driver ]; driver ] in
  let run () = let _, v, _ = run_traced dir prog in v in
  check "the loaded v2 functor migrates v1's state"
    (run () = {|"v2 for jam (was: keep going)"|});
  Sys.remove (Filename.concat dir "appv2.sceo");
  check "a missing upgrade falls back to v1"
    (contains (run ()) "still v1: keep going")

(* ---------------- the linker written in the language ---------------- *)

let () =
  print_endline "\n-- linker --";
  let dir = fixture "linker" in
  let step = compile_exn dir "step.sce" in
  let host = compile_exn dir "host.sce" in
  Units.Artifact.save (Filename.concat dir "step.sceo") step;
  let prog = link_exn [ Units.Host.loader [ host ]; host ] in
  let _, v, _ = run_traced dir prog in
  check "a hand-written link of a loaded functor agrees with the builtin"
    (v = {|"hand-written link = builtin link, both halves kept"|})

(* ---------------- environments as values ---------------- *)

let () =
  print_endline "\n-- worlds --";
  let dir = fixture "worlds" in
  let fancy = compile_exn dir "fancy.sce" in
  let host = compile_exn dir "host.sce" in
  Units.Artifact.save (Filename.concat dir "fancy.sceo") fancy;
  let prog = link_exn [ Units.Host.loader [ host ]; host ] in
  let _, v, _ = run_traced dir prog in
  check "a loaded world is entered with box; a failed load re-enters the snapshot"
    (v = {|"** hello ** / hello"|})

(* ---------------- a lambda-calculus interpreter ---------------- *)

let () =
  print_endline "\n-- lambda --";
  let dir = fixture "lambda" in
  let units =
    List.map (compile_exn dir)
      [ "lexer.sce"; "parser.sce"; "eval.sce"; "pretty.sce"; "main.sce" ]
  in
  let prog = link_exn (Units.Host.str :: units) in
  let _, v, _ = run_traced dir prog in
  check "lex, parse, normalize, print: Church 2+2 = 4; errors are values"
    (v = {|"\\f. \\x. f (f (f (f x)))  ;  a  ;  parse error: expected ')'"|})

(* ---------------- the same case studies, through wasm ----------------

   Trace differential: a capability-bearing program compiled to wasm and run
   under node must print the same lines in the same order and render the same
   value as the interpreter. Runtime loads name .sceo artifacts; at the wasm
   level the host loads the .wasm sibling, so paths inside values are mapped
   before comparing. *)

let have cmd = Sys.command (Printf.sprintf "%s >/dev/null 2>&1" cmd) = 0

let run_js = Filename.concat (Sys.getcwd ()) "../lib/wasm/run.js"

let node_run ~dir args =
  let out = Filename.temp_file "runtime" ".out" in
  let st =
    Sys.command
      (Printf.sprintf "cd %s && node %s %s > %s 2>&1" dir run_js args out)
  in
  let text = String.trim (read_file out) in
  Sys.remove out;
  (st, text)

(* replace every ".sceo" with ".wasm" *)
let wasmify s =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if !i + 5 <= n && String.sub s !i 5 = ".sceo" then begin
      Buffer.add_string b ".wasm";
      i := !i + 5
    end
    else begin
      Buffer.add_char b s.[!i];
      incr i
    end
  done;
  Buffer.contents b

let write_unit_wasm dir (a : Units.Artifact.t) =
  let customs = [ ("sce.slot", Units.Artifact.print_typ (Units.Artifact.slot_typ a)) ] in
  write_file
    (Filename.concat dir (a.a_name ^ ".wasm"))
    (Wasm_backend.Compile.to_binary ~customs a.a_core)

(* Interpreter reference vs node output: same trace, then the same value. *)
let agree name ~dir linked ~units =
  let _, v, trace = run_traced dir linked in
  List.iter (write_unit_wasm dir) units;
  let _, term = Units.Linker.runnable linked in
  write_file (Filename.concat dir "prog.wasm")
    (Wasm_backend.Compile.to_binary term);
  let st, text = node_run ~dir "prog.wasm" in
  let expected = String.concat "\n" (trace @ [ wasmify v ]) in
  if st = 0 && text = expected then check name true
  else (
    check name false;
    Printf.printf "        interpreter:\n%s\n        wasm:\n%s\n" expected text)

(* The same comparison with every unit as its own wasm module behind a link
   module — the wasm-level linking path, runtime loads included. *)
let wasm_level name ~dir arts ~loads =
  let _, v, trace = run_traced dir (link_exn arts) in
  List.iter (write_unit_wasm dir) (arts @ loads);
  let names, unit_types, body = Units.Linker.wasm_parts arts in
  write_file (Filename.concat dir "wlinked.wasm")
    (Wasm_backend.Compile.link_binary ~names ~unit_types body);
  let mods =
    "wlinked.wasm"
    :: List.map (fun (a : Units.Artifact.t) -> a.a_name ^ ".wasm") arts
  in
  let st, text = node_run ~dir (String.concat " " mods) in
  let expected = String.concat "\n" (trace @ [ wasmify v ]) in
  if st = 0 && text = expected then check name true
  else (
    check name false;
    Printf.printf "        interpreter:\n%s\n        wasm:\n%s\n" expected text)

let () =
  if not (have "node --version") then
    print_endline "\nwasm trace differential skipped: node is not installed"
  else begin
    print_endline "\n-- wasm trace differential --";
    (* effects, compiled whole *)
    let dir = fixture "effects" in
    let app = compile_exn dir "app.sce" in
    agree "effects: wasm trace = interpreter trace" ~dir
      (link_exn [ sys; app ]) ~units:[];
    (* effects again, with sys as its own wasm module behind the link module *)
    let names, unit_types, body = Units.Linker.wasm_parts [ sys; app ] in
    List.iter (write_unit_wasm dir) [ sys; app ];
    write_file (Filename.concat dir "linked.wasm")
      (Wasm_backend.Compile.link_binary ~names ~unit_types body);
    let st, text = node_run ~dir "linked.wasm sys.wasm app.wasm" in
    check "effects: sys as a wasm module behind the link module"
      (st = 0
      && text
         = "[app] greeting world\n[app] greeting again\n\
            \"hello, world / hello, again\"");
    (* construction-time effects stay single-shot through wasm *)
    let dir = fixture "boot" in
    let provider = compile_exn dir "provider.sce" in
    let consumer = compile_exn dir "consumer.sce" in
    let arts = [ sys; provider; consumer ] in
    agree "boot: wasm construction trace agrees with the interpreter" ~dir
      (link_exn arts) ~units:[];
    wasm_level "boot: wasm-level link agrees with the interpreter" ~dir arts
      ~loads:[];
    (* the plugin manager: runtime loads happen inside the wasm host *)
    let dir = fixture "plugins" in
    let shout = compile_exn dir "shout.sce" in
    let quiet = compile_exn dir "quiet.sce" in
    let manager = compile_exn dir "manager.sce" in
    Units.Artifact.save (Filename.concat dir "shout.sceo") shout;
    Units.Artifact.save (Filename.concat dir "quiet.sceo") quiet;
    let arts = [ sys; Units.Host.loader [ manager ]; manager ] in
    agree "plugins: wasm loads and traces agree with the interpreter" ~dir
      (link_exn arts) ~units:[ shout; quiet ];
    wasm_level "plugins: wasm-level link agrees with the interpreter" ~dir arts
      ~loads:[ shout; quiet ];
    (* two versions of one module, v2 arriving through the wasm loader *)
    let dir = fixture "versions" in
    let v1 = compile_exn dir "libv1.sce" in
    let v2 = compile_exn dir "libv2.sce" in
    let client = compile_exn dir "client.sce" in
    Units.Artifact.save (Filename.concat dir "libv2.sceo") v2;
    let arts = [ v1; Units.Host.loader [ client ]; client ] in
    agree "versions: wasm agrees with the interpreter" ~dir (link_exn arts)
      ~units:[ v2 ];
    wasm_level "versions: wasm-level link agrees with the interpreter" ~dir
      arts ~loads:[ v2 ];
    (* dynamic upgrade with state handoff *)
    let dir = fixture "upgrade" in
    let av1 = compile_exn dir "appv1.sce" in
    let av2 = compile_exn dir "appv2.sce" in
    let driver = compile_exn dir "driver.sce" in
    Units.Artifact.save (Filename.concat dir "appv2.sceo") av2;
    let arts = [ av1; Units.Host.loader [ driver ]; driver ] in
    agree "upgrade: wasm migration agrees with the interpreter" ~dir
      (link_exn arts) ~units:[ av2 ];
    wasm_level "upgrade: wasm-level link agrees with the interpreter" ~dir arts
      ~loads:[ av2 ];
    (* the lambda-calculus interpreter, str as a host capability *)
    let dir = fixture "lambda" in
    let lunits =
      List.map (compile_exn dir)
        [ "lexer.sce"; "parser.sce"; "eval.sce"; "pretty.sce"; "main.sce" ]
    in
    let arts = Units.Host.str :: lunits in
    agree "lambda: wasm agrees with the interpreter" ~dir (link_exn arts)
      ~units:[];
    wasm_level "lambda: wasm-level link agrees with the interpreter" ~dir arts
      ~loads:[];
    (* the hand-written link of a loaded functor *)
    let dir = fixture "linker" in
    let step = compile_exn dir "step.sce" in
    let host = compile_exn dir "host.sce" in
    Units.Artifact.save (Filename.concat dir "step.sceo") step;
    let arts = [ Units.Host.loader [ host ]; host ] in
    agree "linker: wasm agrees with the interpreter" ~dir (link_exn arts)
      ~units:[ step ];
    wasm_level "linker: wasm-level link agrees with the interpreter" ~dir arts
      ~loads:[ step ];
    (* boxes entering loaded worlds and snapshots *)
    let dir = fixture "worlds" in
    let fancy = compile_exn dir "fancy.sce" in
    let host = compile_exn dir "host.sce" in
    Units.Artifact.save (Filename.concat dir "fancy.sceo") fancy;
    let arts = [ Units.Host.loader [ host ]; host ] in
    agree "worlds: wasm agrees with the interpreter" ~dir (link_exn arts)
      ~units:[ fancy ];
    wasm_level "worlds: wasm-level link agrees with the interpreter" ~dir arts
      ~loads:[ fancy ]
  end

let () =
  print_newline ();
  if !failures = 0 then print_endline "all runtime tests passed"
  else (
    Printf.printf "%d runtime test(s) failed\n" !failures;
    exit 1)
