(* Whole programs: main.exe FILE.sce runs one; with no argument, a REPL where
   each entry is a program submitted with a blank line. *)

let read_file path =
  let ic = open_in_bin path in
  let src = really_input_string ic (in_channel_length ic) in
  close_in ic;
  src

let report src =
  match Sce.Pipeline.run src with
  | Ok o ->
    Printf.printf "- : %s = %s\n" (Sce.Pipeline.type_string o)
      (Sce.Pipeline.value_string o)
  | Error e -> print_endline (Sce.Pipeline.render ~src e)

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
    | None -> print_newline (); submit ()
    | Some line ->
      if String.trim line = "" then submit ()
      else (Buffer.add_string buf line; Buffer.add_char buf '\n');
      loop ()
  in
  loop ()

let () =
  match Array.to_list Sys.argv with
  | _ :: path :: _ -> report (read_file path)
  | _ -> repl ()
