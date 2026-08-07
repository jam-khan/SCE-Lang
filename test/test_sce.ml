let check name condition =
  if condition then Printf.printf "PASS  %s\n" name
  else (
    Printf.printf "FAIL  %s\n" name;
    exit 1)

let eval_string src =
  match Sce.Driver.parse src with
  | Ok ast -> Some (Sce.Interp.eval ast)
  | Error _ -> None

let () =
  check "1 + 1 evaluates to 2" (eval_string "1 + 1" = Some 2);
  check "precedence: 1 + 2 * 3 evaluates to 7" (eval_string "1 + 2 * 3" = Some 7);
  check "parens: (1 + 2) * 3 evaluates to 9" (eval_string "(1 + 2) * 3" = Some 9);
  check "syntax error is reported at the right position"
    (match Sce.Driver.parse "1 + " with
    | Error { line = 1; col = 4; _ } -> true
    | _ -> false);
  print_endline "all tests passed"
