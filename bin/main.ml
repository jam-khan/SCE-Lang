(* Whole programs:  main.exe FILE.sce            run
                    main.exe --wasm OUT FILE.sce  compile to wasm
   Units:           main.exe -c FILE.sce -o FILE.sceo      compile (+ .scei per module)
                    main.exe --link A.sceo B.sceo -o OUT   link, left to right
                    main.exe --run ART.sceo                evaluate a linked artifact
                    main.exe --wasm OUT ART.sceo           emit wasm for a linked artifact
   With no argument, a REPL where each entry is a whole program submitted with
   a blank line. *)

let report src =
  match Sce.Pipeline.run src with
  | Ok o ->
    Printf.printf "- : %s = %s\n" (Sce.Pipeline.type_string o)
      (Sce.Pipeline.value_string o)
  | Error e -> print_endline (Sce.Pipeline.render ~src e)

let run_file path =
  let ic = open_in_bin path in
  let src = really_input_string ic (in_channel_length ic) in
  close_in ic;
  report src

let repl () =
  print_endline
    "SCE repl — enter a program, then a blank line to run it (Ctrl-D to exit)";
  let buf = Buffer.create 256 in
  let submit () =
    let src = Buffer.contents buf in
    Buffer.clear buf;
    if String.trim src <> "" then report src
  in
  let rec loop () =
    print_string (if Buffer.length buf = 0 then "> " else "  ");
    flush stdout;
    match In_channel.input_line In_channel.stdin with
    | None ->
      print_newline ();
      submit ()
    | Some line ->
      if String.trim line = "" then submit ()
      else (
        Buffer.add_string buf line;
        Buffer.add_char buf '\n');
      loop ()
  in
  loop ()

(* Compile to wasm rather than interpreting. `--wat` writes the text form
   alongside, which is the quickest way to see what the backend emitted. *)
let compile_file ~out ?wat path =
  let ic = open_in_bin path in
  let src = really_input_string ic (in_channel_length ic) in
  close_in ic;
  match Sce.Pipeline.run_to_core src with
  | Error e -> print_endline (Sce.Pipeline.render ~src e); exit 1
  | Ok core ->
    let write file contents =
      let oc = open_out_bin file in
      output_string oc contents;
      close_out oc
    in
    write out (Wasm_backend.Compile.to_binary core);
    (match wat with Some f -> write f (Wasm_backend.Compile.to_wat core) | None -> ());
    Printf.printf "wrote %s\n" out

let read_file path =
  let ic = open_in_bin path in
  let src = really_input_string ic (in_channel_length ic) in
  close_in ic;
  src

let write_file path contents =
  let oc = open_out_bin path in
  output_string oc contents;
  close_out oc

let or_die = function
  | Ok v -> v
  | Error (e : Sce.Pipeline.error) ->
    Printf.eprintf "%s error: %s\n" e.stage e.message;
    exit 1

let compile_unit ~out src_path =
  let src = read_file src_path in
  match Sce.Pipeline.compile_unit ~path:src_path src with
  | Error e ->
    print_endline (Sce.Pipeline.render ~src e);
    exit 1
  | Ok (art, sceis) ->
    Sce.Sepcomp.save_artifact out art;
    let dir = Filename.dirname out in
    List.iter
      (fun (name, contents) -> write_file (Filename.concat dir name) contents)
      sceis;
    Printf.printf "wrote %s%s\n" out
      (match sceis with
       | [] -> ""
       | _ -> " (+ " ^ String.concat ", " (List.map fst sceis) ^ ")")

let link_artifacts paths ~out =
  let arts = List.map Sce.Sepcomp.load_artifact paths in
  let linked = or_die (Sce.Pipeline.link_artifacts arts) in
  Sce.Sepcomp.save_artifact out linked;
  Printf.printf "wrote %s (%s)\n" out linked.Sce.Sepcomp.a_name

let run_artifact path =
  let art = Sce.Sepcomp.load_artifact path in
  let t, v = or_die (Sce.Pipeline.run_artifact art) in
  Printf.printf "- : %s = %s\n" t v

let wasm_of_artifact ~out ?wat path =
  let art = Sce.Sepcomp.load_artifact path in
  let _, term = Sce.Sepcomp.runnable art in
  write_file out (Wasm_backend.Compile.to_binary term);
  (match wat with
   | Some f -> write_file f (Wasm_backend.Compile.to_wat term)
   | None -> ());
  Printf.printf "wrote %s\n" out

let is_artifact path = Filename.check_suffix path ".sceo"

let rec split_link args =
  match args with
  | [] -> failwith "--link needs -o OUT"
  | [ "-o"; out ] -> ([], out)
  | "-o" :: _ -> failwith "--link needs -o OUT last"
  | a :: rest ->
    let more, out = split_link rest in
    (a :: more, out)

let () =
  try
    match Array.to_list Sys.argv with
    | _ :: "-c" :: src :: "-o" :: out :: [] -> compile_unit ~out src
    | _ :: "--link" :: rest ->
      let paths, out = split_link rest in
      link_artifacts paths ~out
    | _ :: "--run" :: path :: [] -> run_artifact path
    | _ :: "--wasm" :: out :: path :: rest ->
      let wat = match rest with "--wat" :: f :: _ -> Some f | _ -> None in
      if is_artifact path then wasm_of_artifact ~out ?wat path
      else compile_file ~out ?wat path
    | _ :: path :: _ -> run_file path
    | _ -> repl ()
  with
  | Sce.Sepcomp.Error m | Failure m ->
    Printf.eprintf "error: %s\n" m;
    exit 1
