(* `main.exe FILE.sce` runs a program; `--wasm OUT.wasm FILE.sce` compiles it
   instead. With no argument it starts a REPL where each entry is a whole
   program, submitted with a blank line. *)

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

let () =
  match Array.to_list Sys.argv with
  | _ :: "--wasm" :: out :: path :: rest ->
    let wat = match rest with "--wat" :: f :: _ -> Some f | _ -> None in
    compile_file ~out ?wat path
  | _ :: path :: _ -> run_file path
  | _ -> repl ()
