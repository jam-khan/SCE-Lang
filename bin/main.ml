let () =
  print_endline "SCE repl — type an arithmetic expression (Ctrl-D to exit)";
  let rec loop () =
    print_string "> ";
    flush stdout;
    match In_channel.input_line In_channel.stdin with
    | None -> print_newline ()
    | Some line ->
        (if String.trim line <> "" then
           match Sce.Driver.parse line with
           | Ok ast -> (
               match Sce.Interp.eval ast with
               | value ->
                   Printf.printf "%s = %d\n" (Sce.Ast.string_of_expr ast) value
               | exception Division_by_zero ->
                   print_endline "runtime error: division by zero")
           | Error err -> print_endline (Sce.Driver.render ~src:line err));
        loop ()
  in
  loop ()
