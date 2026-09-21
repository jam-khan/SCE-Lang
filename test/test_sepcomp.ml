(* Separate compilation: units, interfaces, the core linker.

   Fixtures are written to a temp directory and driven through the same
   Pipeline entry points the CLI uses, so these tests cover the .scei loop
   (generation -> auto-import) exactly as a user hits it. *)

let failures = ref 0

let check name condition =
  if condition then Printf.printf "PASS  %s\n" name
  else (
    Printf.printf "FAIL  %s\n" name;
    incr failures)

let dir =
  let d = Filename.temp_file "sepcomp" "" in
  Sys.remove d;
  Sys.mkdir d 0o755;
  d

let path name = Filename.concat dir name

let write name contents =
  let oc = open_out_bin (path name) in
  output_string oc contents;
  close_out oc

let counter_src =
  "module Counter = struct\n\
  \  let start : Int = 10\n\
  \  let bump (n : Int) : Int = n + 1\n\
   end\n"

let fmt_src =
  "module Fmt = struct\n\
  \  let bracket (s : String) : String = \"[\" ^ s ^ \"]\"\n\
  \  let yes (b : Bool) : String = if b then \"yes\" else \"no\"\n\
   end\n"

let app_src =
  "import Counter\n\
   import Fmt\n\n\
   module App = struct\n\
  \  let level : Int = Counter.bump (Counter.bump Counter.start)\n\
  \  let big : Bool = level > 11\n\
   end\n\n\
   let main : String = Fmt.bracket (Fmt.yes App.big)\n"

(* The same program as one file, for the differential check. *)
let whole_src =
  "module Counter = struct\n\
  \  let start : Int = 10\n\
  \  let bump (n : Int) : Int = n + 1\n\
   end\n\
   module Fmt = struct\n\
  \  let bracket (s : String) : String = \"[\" ^ s ^ \"]\"\n\
  \  let yes (b : Bool) : String = if b then \"yes\" else \"no\"\n\
   end\n\
   module App = struct\n\
  \  let level : Int = Counter.bump (Counter.bump Counter.start)\n\
  \  let big : Bool = level > 11\n\
   end\n\
   let main = Fmt.bracket (Fmt.yes App.big)\n"

let compile name src =
  write name src;
  match Sce.Pipeline.compile_unit ~path:(path name) src with
  | Ok (art, sceis) ->
    List.iter (fun (n, c) -> write n c) sceis;
    Ok art
  | Error e -> Error e

let compile_exn name src =
  match compile name src with
  | Ok a -> a
  | Error e -> failwith (name ^ ": " ^ e.stage ^ ": " ^ e.message)

let compile_err name src =
  match compile name src with Ok _ -> None | Error e -> Some e

let link_err arts =
  match Sce.Pipeline.link_artifacts arts with
  | Ok _ -> None
  | Error e -> Some e.message

let () = print_endline "-- units and interfaces --"

let counter = compile_exn "counter.sce" counter_src
let fmt = compile_exn "fmt.sce" fmt_src

let () =
  check "leaf units have no imports"
    (counter.a_imports = None && fmt.a_imports = None);
  check "compiling a provider generates its module interface"
    (Sys.file_exists (path "Counter.scei") && Sys.file_exists (path "Fmt.scei"))

let app = compile_exn "app.sce" app_src

let () =
  check "auto import resolves against generated .scei" (app.a_imports <> None);
  (* the artifact round-trips through disk *)
  Units.Artifact.save (path "app.sceo") app;
  let app' = Units.Artifact.load (path "app.sceo") in
  check "artifact save/load round-trips" (app' = app);
  (* interface printer inverts the parser on every stored type *)
  let roundtrips t =
    Units.Artifact.parse_typ ~what:"test" (Units.Artifact.print_typ t) = t
  in
  check "print/parse round-trip: exports"
    (List.for_all roundtrips
       [ counter.a_exports; fmt.a_exports; app.a_exports;
         Option.get app.a_imports ]);
  check "round-trip covers mu and =>"
    (List.for_all roundtrips
       [
         Units.Artifact.parse_typ ~what:"t" "mu a. Top | a";
         Units.Artifact.parse_typ ~what:"t"
           "{ a : Int } => { b : mu a. Top | (a & { c : Int -> Int }) }";
       ])

let () = print_endline "\n-- linking --"

let linked =
  match Sce.Pipeline.link_artifacts [ counter; fmt; app ] with
  | Ok a -> a
  | Error e -> failwith e.message

let () =
  check "linked artifact has no imports" (linked.a_imports = None);
  (match Sce.Pipeline.run_artifact linked with
   | Ok (t, v) ->
     check "linked program runs main" (t = "String" && v = {|"[yes]"|})
   | Error _ -> check "linked program runs main" false);
  (* differential: the same program as one file *)
  (match Sce.Pipeline.run whole_src with
   | Ok o ->
     check "linked value equals the whole-program value"
       (Sce.Pipeline.value_string o = {|"[yes]"|})
   | Error _ -> check "linked value equals the whole-program value" false);
  (* the linked term is closed: any environment gives the same value *)
  let render e v =
    Core_lambdae.Pretty.exp_to_string (Core_lambdae.Eval.eval e v)
  in
  let junk =
    Core_lambdae.Ast.(Mrg (Lit (Int 1), Lrec ("junk", Lit (Bool true))))
  in
  check "linked term is insensitive to the environment"
    (render Core_lambdae.Ast.Unit linked.a_core = render junk linked.a_core)

let () = print_endline "\n-- wasm: core-linked and wasm-linked --"

let have cmd = Sys.command (Printf.sprintf "%s >/dev/null 2>&1" cmd) = 0

let node_run args =
  let out = path "node.out" in
  let st = Sys.command (Printf.sprintf "node ../lib/wasm/run.js %s > %s 2>&1" args out) in
  let ic = open_in_bin out in
  let text = String.trim (really_input_string ic (in_channel_length ic)) in
  close_in ic;
  (st, text)

let () =
  if not (have "node --version") then
    print_endline "skipped: node is not installed"
  else begin
    (* path A: link at core, compile the linked artifact whole *)
    let _, term = Units.Linker.runnable linked in
    write "prog.wasm" (Wasm_backend.Compile.to_binary term);
    let st, text = node_run (path "prog.wasm") in
    check "wasm of the core-linked artifact agrees with the interpreter"
      (st = 0 && text = {|"[yes]"|});
    (* path B: compile each unit to its own module, link at the wasm level *)
    List.iter
      (fun (a : Units.Artifact.t) ->
        write (a.a_name ^ ".wasm") (Wasm_backend.Compile.to_binary a.a_core))
      [ counter; fmt; app ];
    let names, unit_types, body = Units.Linker.wasm_parts [ counter; fmt; app ] in
    write "linked.wasm" (Wasm_backend.Compile.link_binary ~names ~unit_types body);
    let st, text =
      node_run
        (String.concat " "
           (List.map path [ "linked.wasm"; "counter.wasm"; "fmt.wasm"; "app.wasm" ]))
    in
    check "wasm-linked multi-module program agrees with everything else"
      (st = 0 && text = {|"[yes]"|});
    (* the manifest rejects units out of order *)
    let st, _ =
      node_run
        (String.concat " "
           (List.map path [ "linked.wasm"; "fmt.wasm"; "counter.wasm"; "app.wasm" ]))
    in
    check "the unit manifest rejects a wrong instantiation order" (st <> 0);
    if have "wasm-opt --version" then
      List.iter
        (fun f ->
          check ("binaryen validates " ^ f)
            (Sys.command
               (Printf.sprintf
                  "wasm-opt --enable-gc --enable-reference-types \
                   --enable-bulk-memory %s -o /dev/null 2>/dev/null"
                  (path f))
             = 0))
        [ "counter.wasm"; "fmt.wasm"; "app.wasm"; "linked.wasm" ]
  end

let () = print_endline "\n-- import forms --"

let () =
  (* named interface file *)
  write "counterIntf.scei" "{start : Int} & {bump : Int -> Int}\n";
  let named_src = "import Counter : counterIntf\nlet main : Int = Counter.start\n" in
  check "import via named .scei"
    (match compile "named.sce" named_src with Ok _ -> true | Error _ -> false);
  (* inline interface *)
  let inline_src =
    "import Counter : sig { start : Int } & { bump : Int -> Int } end\n\
     let main : Int = Counter.bump Counter.start\n"
  in
  (match compile "inline.sce" inline_src with
   | Ok a ->
     check "import via inline type" true;
     check "inline import links and runs"
       (match Sce.Pipeline.link_artifacts [ counter; a ] with
        | Ok l -> Sce.Pipeline.run_artifact l = Ok ("Int", "11")
        | Error _ -> false)
   | Error _ ->
     check "import via inline type" false;
     check "inline import links and runs" false)

let () = print_endline "\n-- rejected --"

let contains hay needle =
  let nh = String.length hay and nn = String.length needle in
  let rec go i = i + nn <= nh && (String.sub hay i nn = needle || go (i + 1)) in
  nn = 0 || go 0

let expect name err_opt (stage, needle) =
  match err_opt with
  | Some (e : Sce.Pipeline.error) ->
    let ok =
      e.stage = stage && contains e.message needle
    in
    if ok then check name true
    else (
      check name false;
      Printf.printf "        got %s: %s\n" e.stage e.message)
  | None -> check name false

let () =
  expect "missing .scei"
    (compile_err "noscei.sce" "import Missing\nlet main : Int = 1\n")
    ("desugar", "Missing.scei not found");
  expect "whole-program file cannot import"
    (match Sce.Pipeline.run "import Counter\nlet main = 1" with
     | Error e -> Some e
     | Ok _ -> None)
    ("desugar", "unit");
  (* the imports record is synthesized by unit_wrapper; it must still carry a
     real location, or this reports at the dummy 1:0 *)
  (match
     compile_err "dupimport.sce" "import Counter\nimport Counter\nlet main : Int = 1\n"
   with
   | Some e ->
     check "duplicate imports report a real location"
       (contains e.message "duplicate label" && e.line = 1 && e.col = 7)
   | None -> check "duplicate imports report a real location" false);
  (match link_err [ app ] with
   | Some m -> check "first unit must be a leaf" (String.length m > 0)
   | None -> check "first unit must be a leaf" false);
  (match link_err [ counter; counter ] with
   | Some m ->
     check "duplicate exports are rejected" (contains m "both export")
   | None -> check "duplicate exports are rejected" false);
  (match link_err [ fmt; app ] with
   | Some m ->
     check "unsatisfied import is rejected" (contains m "no linked provider")
   | None -> check "unsatisfied import is rejected" false);
  (* stale interface: consumer compiled against a wrong Counter.scei *)
  write "Counter.scei" "{start : Int}\n";
  (match compile "stale.sce" "import Counter\nlet main : Int = Counter.start\n" with
   | Ok stale ->
     (match link_err [ counter; stale ] with
      | Some m ->
        check "stale .scei is caught at link time" (contains m "stale")
      | None -> check "stale .scei is caught at link time" false)
   | Error _ -> check "stale .scei is caught at link time" false);
  (* restore the good interface for anyone after us *)
  write "Counter.scei" (Units.Artifact.print_typ
    (match Sce_core.Elab.srlookup_opt counter.a_exports "Counter" with
     | Some t -> t
     | None -> failwith "no Counter export") ^ "\n");
  (* an unreadable artifact is a clean error *)
  write "bad.sceo" "not an artifact at all";
  check "bad artifact magic is a clean error"
    (match Units.Artifact.load (path "bad.sceo") with
     | exception Units.Artifact.Error _ -> true
     | _ -> false)

let () =
  print_newline ();
  if !failures = 0 then print_endline "all sepcomp tests passed"
  else (
    Printf.printf "%d sepcomp test(s) failed\n" !failures;
    exit 1)
