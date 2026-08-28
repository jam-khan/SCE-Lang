let failures = ref 0

let check name condition =
  if condition then Printf.printf "PASS  %s\n" name
  else (Printf.printf "FAIL  %s\n" name; incr failures)

let ok name src typ value =
  match Sce.Pipeline.run src with
  | Ok o ->
    let t = Sce.Pipeline.type_string o and v = Sce.Pipeline.value_string o in
    if t = typ && v = value then check name true
    else (
      check name false;
      Printf.printf "        expected  %s = %s\n        got       %s = %s\n"
        typ value t v)
  | Error e ->
    check name false;
    print_endline (Sce.Pipeline.render ~src e)

let () =
  ok "arithmetic" "let main = 1 + 2 * 3 - 4" "Int" "3";
  ok "let" "let main = let x = 1 in x + 1" "Int" "2";
  ok "application" "let f (x : Int) : Int = x * 2 let main = f 21" "Int" "42";
  ok "let rec"
    "let main = let rec fact (n : Int) : Int = if n <= 1 then 1 else n * fact (n - 1) \
     in fact 5" "Int" "120";
  ok "record and projection" "let main = { a = 1, b = 2 }.b" "Int" "2";
  ok "dependent merge" "let main = { a = 1 } ;; { b = a + 1 }"
    "{a : Int} & {b : Int}" "{ a = 1, b = 2 }";
  ok "structure"
    "module M = struct let a : Int = 2 let b : Int = a * 3 end let main = M.b"
    "Int" "6";
  ok "open" "let main = open { a = 1, b = 2 } in a + b" "Int" "3";
  ok "adt"
    "type shape = | Circle of Int | Rect of Int * Int\n\
     let area (s : shape) : Int =\n\
     \  match s with | Circle r -> r * r * 3 | Rect (w, h) -> w * h end\n\
     let main = area (Rect (4, 5))" "Int" "20";
  if !failures = 0 then print_endline "all tests passed"
  else (Printf.printf "%d test(s) failed\n" !failures; exit 1)
