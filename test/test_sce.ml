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

let rejected name src needle =
  match Sce.Pipeline.run src with
  | Ok _ -> check name false
  | Error e ->
    let n = String.length needle and m = e.message in
    let rec go i = i + n <= String.length m && (String.sub m i n = needle || go (i + 1)) in
    check name (go 0)

(* the elaborated term, as the paper's figures give it *)
let core name src expected =
  match Sce.Pipeline.run src with
  | Ok o ->
    let c = Sce.Pipeline.core_string o in
    if c = expected then check name true
    else (
      check name false;
      Printf.printf "        expected  %s\n        got       %s\n" expected c)
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
  (* the module layer, rule by rule *)
  ok "Elab-Str: a structure has a signature type"
    "let main = struct let a : Int = 1 end" "sig {a : Int} end" "{ a = 1 }";
  ok "Ctm-Sig: selection looks through a signature"
    "let main = (struct let a : Int = 1 end ; { b = 2 }).a" "Int" "1";
  rejected "a structure is not its body: direct application is ill typed"
    "module F (X : { a : Int }) = struct let b : Int = X.a end\n\
     let main = F(struct let a : Int = 1 end)" "functor argument type mismatch";
  ok "Elab-Link: linking selects the import from a structure"
    "let main = (link struct let a : Int = 1 let c : Int = 5 end\n\
     with sandbox functor (X : { a : Int }) -> struct let b : Int = X.a + 1 end).b"
    "Int" "2";
  rejected "Elab-NMrg: the right operand cannot see the left"
    "let main = { a = 1 } ; { b = a }" "unbound variable";
  (* the outer `(_ ; ?.[0]).[0]` is the top-level `let main` itself *)
  core "Elab-Let" "let main = let x = 1 in x" "((1 ; ?.[0]).[0] ; ?.[0]).[0]";
  core "Elab-NMrg" "let main = { a = 1 } ; { b = 2 }"
    "((? ; ((box ?.[0] in { a = 1 }) ; (box ?.[1] in { b = 2 }))).[0] ; ?.[0]).[0]";
  if !failures = 0 then print_endline "all tests passed"
  else (Printf.printf "%d test(s) failed\n" !failures; exit 1)
