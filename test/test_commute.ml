(* Linking commutation over the case studies in examples/units/.

   Each directory holds a set of units and `whole.sce`, the same program as
   one file. Every path through the toolchain must produce the same value:

     1  whole program, interpreted
     2  whole program, compiled to wasm and run under node
     3  units linked at the core level, evaluated
     3b the same units linked *incrementally* (a linked artifact is itself a
        leaf unit, so linking left-folds two at a time)
     3c an alternative link order, where the dependencies allow one
     4  the core-linked term compiled to wasm and run under node
     5  units compiled to separate wasm modules, linked at the wasm level

   The wasm paths are skipped when node is not installed. *)

let failures = ref 0

let check name condition =
  if condition then Printf.printf "PASS  %s\n" name
  else (
    Printf.printf "FAIL  %s\n" name;
    incr failures)

let examples_dir = "../examples/units"
let run_js = "../lib/wasm/run.js"

let have cmd = Sys.command (Printf.sprintf "%s >/dev/null 2>&1" cmd) = 0
let with_node = have "node --version"
let with_wasm_opt = have "wasm-opt --version"

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
  let d = Filename.temp_file "commute" "" in
  Sys.remove d;
  Sys.mkdir d 0o755;
  d

let node_run args =
  let out = Filename.temp_file "commute" ".out" in
  let st = Sys.command (Printf.sprintf "node %s %s > %s 2>&1" run_js args out) in
  let text = String.trim (read_file out) in
  Sys.remove out;
  (st, text)

let validates path =
  Sys.command
    (Printf.sprintf
       "wasm-opt --enable-gc --enable-reference-types --enable-bulk-memory \
        %s -o /dev/null 2>/dev/null" path)
  = 0

(* (directory, units in link order, alternative order if one is legal) *)
let sets =
  [ ("peano", [ "nat"; "arith"; "demo" ], None);
    ("shop", [ "region"; "checkout"; "invoice" ], None) ]

let compile_units dir units =
  List.map
    (fun u ->
      let path = Filename.concat dir (u ^ ".sce") in
      match Sce.Pipeline.compile_unit ~path (read_file path) with
      | Ok (art, sceis) ->
        List.iter (fun (n, c) -> write_file (Filename.concat dir n) c) sceis;
        art
      | Error e -> failwith (u ^ ": " ^ e.stage ^ ": " ^ e.message))
    units

let link_exn arts =
  match Sce.Pipeline.link_artifacts arts with
  | Ok a -> a
  | Error e -> failwith e.message

let run_exn art =
  match Sce.Pipeline.run_artifact art with
  | Ok tv -> tv
  | Error e -> failwith e.message

let commute (set, units, alt_order) =
  Printf.printf "-- %s --\n" set;
  let dir = temp_dir () in
  Array.iter
    (fun f ->
      if Filename.check_suffix f ".sce" then
        write_file (Filename.concat dir f)
          (read_file (Filename.concat (Filename.concat examples_dir set) f)))
    (Sys.readdir (Filename.concat examples_dir set));
  let name what = set ^ ": " ^ what in
  let arts = compile_units dir units in
  (* 1: the reference *)
  let whole_src = read_file (Filename.concat dir "whole.sce") in
  let whole_t, whole_v =
    match Sce.Pipeline.run whole_src with
    | Ok o -> (Sce.Pipeline.type_string o, Sce.Pipeline.value_string o)
    | Error e -> failwith (set ^ "/whole.sce: " ^ e.stage ^ ": " ^ e.message)
  in
  (* 3: one-shot core link *)
  let linked = link_exn arts in
  let t3, v3 = run_exn linked in
  check (name "core link value = whole") (v3 = whole_v);
  check (name "core link type = whole") (t3 = whole_t);
  (* 3b: incremental — a linked artifact is a leaf, so linking left-folds *)
  let incremental =
    match arts with
    | first :: rest -> List.fold_left (fun acc u -> link_exn [ acc; u ]) first rest
    | [] -> assert false
  in
  check (name "incremental link = one-shot link") (run_exn incremental = (t3, v3));
  (* 3c: independent providers may swap places *)
  (match alt_order with
   | None -> ()
   | Some order ->
     let by_name n = List.find (fun (a : Units.Artifact.t) -> a.a_name = n) arts in
     let _, v = run_exn (link_exn (List.map by_name order)) in
     check (name "permuted link order, same main") (v = whole_v));
  if with_node then begin
    (* 2: whole program through wasm *)
    (match Sce.Pipeline.run_to_core whole_src with
     | Ok core ->
       let f = Filename.concat dir "whole.wasm" in
       write_file f (Wasm_backend.Compile.to_binary core);
       let st, text = node_run f in
       check (name "whole-program wasm = whole") (st = 0 && text = whole_v)
     | Error e -> failwith (e.stage ^ ": " ^ e.message));
    (* 4: the core-linked term through wasm *)
    let _, term = Units.Linker.runnable linked in
    let f = Filename.concat dir "linked.wasm" in
    write_file f (Wasm_backend.Compile.to_binary term);
    let st, text = node_run f in
    check (name "core-linked wasm = whole") (st = 0 && text = whole_v);
    (* 5: linked at the wasm level *)
    let unit_wasms =
      List.map
        (fun (a : Units.Artifact.t) ->
          let f = Filename.concat dir (a.a_name ^ ".wasm") in
          write_file f (Wasm_backend.Compile.to_binary a.a_core);
          f)
        arts
    in
    let names, unit_types, body = Units.Linker.wasm_parts arts in
    let lf = Filename.concat dir "wlinked.wasm" in
    write_file lf (Wasm_backend.Compile.link_binary ~names ~unit_types body);
    let st, text = node_run (String.concat " " (lf :: unit_wasms)) in
    check (name "wasm-linked = whole") (st = 0 && text = whole_v);
    if with_wasm_opt then
      check (name "binaryen validates every module")
        (List.for_all validates
           (Filename.concat dir "whole.wasm" :: f :: lf :: unit_wasms))
  end

let () =
  if not with_node then
    print_endline "note: node is not installed; wasm paths are skipped";
  List.iter commute sets;
  print_newline ();
  if !failures = 0 then print_endline "all commutation tests passed"
  else (
    Printf.printf "%d commutation test(s) failed\n" !failures;
    exit 1)
