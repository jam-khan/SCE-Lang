(* Host capabilities and runtime linking (interpreter level).

   Effects are captured by redirecting Sepcomp.host_out, so every test also
   checks the *trace* — which lines were printed, in which order — not just
   the final value. The fixtures are the shipped case studies under
   examples/effects, examples/plugins and examples/dynconfig. *)

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
  let saved_out = !Sce.Sepcomp.host_out in
  let saved_cwd = Sys.getcwd () in
  Sce.Sepcomp.host_out := Buffer.add_string buf;
  Sys.chdir dir;
  let finish () =
    Sce.Sepcomp.host_out := saved_out;
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

let fixture set =
  let src = Filename.concat "../examples" set in
  let dir = temp_dir () in
  Array.iter
    (fun f ->
      if Filename.check_suffix f ".sce" then
        write_file (Filename.concat dir f) (read_file (Filename.concat src f)))
    (Sys.readdir src);
  dir

let sys = Sce.Sepcomp.sys_artifact

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
       (e.stage = "scope" && contains e.message "Sys")
   | Ok _ -> check "a plugin reaching for Sys is a scope error" false);
  (* plugins are loaded at run time from their artifacts *)
  Sce.Sepcomp.save_artifact (Filename.concat dir "shout.sceo") shout;
  Sce.Sepcomp.save_artifact (Filename.concat dir "quiet.sceo") quiet;
  let prog = link_exn [ sys; Sce.Sepcomp.loader_artifact [ manager ]; manager ] in
  (* the linked program survives a disk round-trip, loader and all *)
  Sce.Sepcomp.save_artifact (Filename.concat dir "prog.sceo") prog;
  let prog = Sce.Sepcomp.load_artifact (Filename.concat dir "prog.sceo") in
  let _, v, trace = run_traced dir prog in
  check "plugins run under attenuated capabilities"
    (contains v "shout! (quiet) <");
  check "a missing plugin is a value, not a crash"
    (contains v "ghost.sceo");
  check "plugin effects carry their per-plugin prefix, in order"
    (trace = [ "[shout] making some noise"; "[quiet] staying quiet" ])

(* ---------------- config-driven loading ---------------- *)

let () =
  print_endline "\n-- dynconfig --";
  let dir = fixture "dynconfig" in
  let plain = compile_exn dir "plain.sce" in
  let fancy = compile_exn dir "fancy.sce" in
  let chooser = compile_exn dir "chooser.sce" in
  Sce.Sepcomp.save_artifact (Filename.concat dir "plain.sceo") plain;
  Sce.Sepcomp.save_artifact (Filename.concat dir "fancy.sceo") fancy;
  let prog =
    link_exn [ sys; Sce.Sepcomp.loader_artifact [ chooser ]; chooser ]
  in
  let run () = let _, v, _ = run_traced dir prog in v in
  write_file (Filename.concat dir "skin.txt") "fancy.sceo";
  check "config picks the fancy skin" (run () = {|"** hello **"|});
  write_file (Filename.concat dir "skin.txt") "plain.sceo";
  check "swapping one line of config swaps the implementation"
    (run () = {|"hello"|});
  Sys.remove (Filename.concat dir "skin.txt");
  check "a missing config falls back in-language" (run () = {|"hello"|});
  (* an artifact with the wrong interface is refused by the runtime check *)
  write_file (Filename.concat dir "skin.txt") "prog.sceo";
  Sce.Sepcomp.save_artifact (Filename.concat dir "prog.sceo") prog;
  check "the loader rejects a mismatched interface"
    (contains (run ()) "no skin:")

(* ---------------- the same case studies, through wasm ----------------

   Trace differential: a capability-bearing program compiled to wasm and run
   under node must print the same lines in the same order and render the same
   value as the interpreter. Runtime loads name .sceo artifacts; at the wasm
   level the host loads the .wasm sibling, so paths inside values are mapped
   before comparing. *)

let have cmd = Sys.command (Printf.sprintf "%s >/dev/null 2>&1" cmd) = 0

let run_js = Filename.concat (Sys.getcwd ()) "../wasm/run.js"

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

let write_unit_wasm dir (a : Sce.Sepcomp.artifact) =
  let customs = [ ("sce.slot", Sce.Sepcomp.print_typ (Sce.Sepcomp.slot_typ a)) ] in
  write_file
    (Filename.concat dir (a.a_name ^ ".wasm"))
    (Wasm_backend.Compile.to_binary ~customs a.a_core)

(* Interpreter reference vs node output: same trace, then the same value. *)
let agree name ~dir linked ~units =
  let _, v, trace = run_traced dir linked in
  List.iter (write_unit_wasm dir) units;
  let _, term = Sce.Sepcomp.runnable linked in
  write_file (Filename.concat dir "prog.wasm")
    (Wasm_backend.Compile.to_binary term);
  let st, text = node_run ~dir "prog.wasm" in
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
    let names, unit_types, body = Sce.Sepcomp.wasm_link_parts [ sys; app ] in
    List.iter (write_unit_wasm dir) [ sys; app ];
    write_file (Filename.concat dir "linked.wasm")
      (Wasm_backend.Compile.link_binary ~names ~unit_types body);
    let st, text = node_run ~dir "linked.wasm sys.wasm app.wasm" in
    check "effects: sys as a wasm module behind the link module"
      (st = 0
      && text
         = "[app] greeting world\n[app] greeting again\n\
            \"hello, world / hello, again\"");
    (* the plugin manager: runtime loads happen inside the wasm host *)
    let dir = fixture "plugins" in
    let shout = compile_exn dir "shout.sce" in
    let quiet = compile_exn dir "quiet.sce" in
    let manager = compile_exn dir "manager.sce" in
    Sce.Sepcomp.save_artifact (Filename.concat dir "shout.sceo") shout;
    Sce.Sepcomp.save_artifact (Filename.concat dir "quiet.sceo") quiet;
    agree "plugins: wasm loads and traces agree with the interpreter" ~dir
      (link_exn [ sys; Sce.Sepcomp.loader_artifact [ manager ]; manager ])
      ~units:[ shout; quiet ];
    (* config-driven loading, including the mismatch message *)
    let dir = fixture "dynconfig" in
    let plain = compile_exn dir "plain.sce" in
    let fancy = compile_exn dir "fancy.sce" in
    let chooser = compile_exn dir "chooser.sce" in
    List.iter
      (fun a -> Sce.Sepcomp.save_artifact
          (Filename.concat dir (a.Sce.Sepcomp.a_name ^ ".sceo")) a)
      [ plain; fancy; chooser ];
    let linked =
      link_exn [ sys; Sce.Sepcomp.loader_artifact [ chooser ]; chooser ]
    in
    List.iter
      (fun skin ->
        write_file (Filename.concat dir "skin.txt") skin;
        agree ("dynconfig: wasm agrees on skin = " ^ skin) ~dir linked
          ~units:[ plain; fancy; chooser ])
      [ "fancy.sceo"; "plain.sceo"; "chooser.sceo" ]
  end

let () =
  print_newline ();
  if !failures = 0 then print_endline "all runtime tests passed"
  else (
    Printf.printf "%d runtime test(s) failed\n" !failures;
    exit 1)
