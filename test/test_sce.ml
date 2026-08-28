let failures = ref 0

let check name condition =
  if condition then Printf.printf "PASS  %s\n" name
  else (
    Printf.printf "FAIL  %s\n" name;
    incr failures)

(* ---------------- parsing ---------------- *)

let parses src = match Driver.parse src with Ok _ -> true | Error _ -> false

let parse_exn src =
  match Driver.parse src with
  | Ok p -> p
  | Error e -> failwith (Driver.render ~src e)

let test_parsing () =
  print_endline "-- parsing --";
  List.iter
    (fun (name, src) -> check ("parses: " ^ name) (parses src))
    [
      ("literals", "let main = 1");
      ("arithmetic", "let main = 1 + 2 * 3 - 4 / 2 mod 3");
      ("comparison", "let main = 1 <= 2");
      ("boolean", "let main = true && not false || false");
      ("string concat", {|let main = "a" ^ "b"|});
      ("unit", "let main = ()");
      ("lambda", "let main = fun (x : Int) -> x");
      ("multi-param lambda", "let main = fun (x : Int) (y : Int) -> x + y");
      ("application", "let f (x : Int) : Int = x let main = f 1");
      ("record", "let main = { x = 1, y = 2 }");
      ("empty record", "let main = {}");
      ("field access", "let main = { x = 1 }.x");
      ("index escape hatch", "let main = ?.[0]");
      ("query", "let main = ?");
      ("merges", "let main = { x = 1 } ; { y = 2 } ;; { z = 3 }");
      ("let in", "let main = let x = 1 in x");
      ("let annotated", "let main = let x : Int = 1 in x");
      ("let rec", "let main = let rec f (n : Int) : Int = n in f 1");
      ("if", "let main = if true then 1 else 2");
      ("nested if", "let main = if true then if false then 1 else 2 else 3");
      ("ascription", "let main = (1 : Int)");
      ("union ascription", {|let main = (inl 1 : Int | String)|});
      ("case", {|let main = case (inl 1 : Int | String) of inl n -> n | inr s -> 0 end|});
      ("case leading bar",
       {|let main = case (inl 1 : Int | String) of | inl n -> n | inr s -> 0 end|});
      ("mu type", "let main = (1 : Int)");
      ("fold", "let main = fold 1");
      ("unfold", "let main = unfold 1");
      ("struct", "module M = struct let x : Int = 1 end");
      ("sandbox struct", "module M = sandbox struct let x : Int = 1 end");
      ("functor", "module F (X : { a : Int }) = struct let b : Int = X.a end");
      ("functor expr", "let main = functor (X : { a : Int }) -> X");
      ("sandbox functor", "let main = sandbox functor (X : { a : Int }) -> X");
      ("link", "module A = struct let a : Int = 1 end\n\
                module B = link A with functor (X : { a : Int }) -> X");
      ("linkall", "module A = struct let a : Int = 1 end\n\
                   module B = linkall A with functor (X : { a : Int }) -> X");
      ("open expr", "let main = open { x = 1 } in x");
      ("open decl", "module M = struct let x : Int = 1 end\nopen M");
      ("box", "let main = box { x = 1 } in ?");
      ("type alias", "type P = { x : Int, y : Int }");
      ("arrow type", "type F = Int -> Int");
      ("intersection type", "type I = { x : Int } & { y : Int }");
      ("union type", "type U = Int | String");
      ("recursive type", "type N = mu a. Top | a");
      ("signature type", "type S = { a : Int } => { b : Int }");
      ("comments", "(* a (* nested *) comment *) let main = 1");
      ("no main", "let x : Int = 1");
      ("string escapes", {|let main = "a\nb\t\"c\"\\"|});
      ("adt declaration", "type t = | A | B of Int let main = 1");
      ("adt tuple payload", "type t = | P of Int * Int let main = 1");
      ("adt recursive", "type t = | Leaf | Node of t * t let main = 1");
      ("match", "type t = | A | B of Int let main = match A with | A -> 0 | B n -> n end");
      ("match wildcard", "type t = | A | B of Int let main = match A with | A -> 0 | _ -> 1 end");
      ("match tuple pattern",
       "type t = | P of Int * Int let main = match P (1, 2) with P (a, b) -> a + b end");
      ("tuple expression", "let main = (1, 2)._1");
    ];

  List.iter
    (fun (name, src) -> check ("rejects: " ^ name) (not (parses src)))
    [
      ("unclosed paren", "let main = (1");
      ("case without end", {|let main = case x of inl a -> 1 | inr b -> 2|});
      ("if without else", "let main = if true then 1");
      ("unannotated param", "let main = fun x -> x");
      ("unterminated string", {|let main = "abc|});
      ("unterminated comment", "(* abc let main = 1");
      ("bad character", "let main = 1 @ 2");
      ("match without end", "type t = | A let main = match A with | A -> 0");
      ("adt constructor without type", "type t = | A of let main = 1");
    ];

  (* precedence and associativity *)
  let open Ast in
  (* the parser no longer builds `main`; it is an ordinary `let main` decl *)
  let main src =
    match (parse_exn src).decls with
    | [ { it = DLet b; _ } ] -> b.b_exp
    | _ -> assert false
  in
  check "precedence: * binds tighter than +"
    (match (main "let main = 1 + 2 * 3").it with
     | EBinop (Add, _, { it = EBinop (Mul, _, _); _ }) -> true
     | _ -> false);
  check "associativity: - is left"
    (match (main "let main = 1 - 2 - 3").it with
     | EBinop (Sub, { it = EBinop (Sub, _, _); _ }, _) -> true
     | _ -> false);
  check "associativity: ^ is right"
    (match (main {|let main = "a" ^ "b" ^ "c"|}).it with
     | EBinop (Cat, _, { it = EBinop (Cat, _, _); _ }) -> true
     | _ -> false);
  check "field access binds tighter than application"
    (match (main "let main = f x.l").it with
     | EApp (_, { it = EField _; _ }) -> true
     | _ -> false);
  check "arrow type is right associative"
    (match (parse_exn "type T = Int -> Int -> Int").decls with
     | [ { it = DType (_, { it = TArr (_, { it = TArr _; _ }); _ }); _ } ] -> true
     | _ -> false);
  check "& binds tighter than | in types"
    (match (parse_exn "type T = Int & Top | String").decls with
     | [ { it = DType (_, { it = TOr ({ it = TAnd _; _ }, _); _ }); _ } ] -> true
     | _ -> false);
  check "mu extends maximally right"
    (match (parse_exn "type T = mu a. Top | a").decls with
     | [ { it = DType (_, { it = TMu (_, { it = TOr _; _ }); _ }); _ } ] -> true
     | _ -> false);
  check "syntax error carries position"
    (match Driver.parse "let main = 1 +" with
     | Error { line = 1; _ } -> true
     | _ -> false)

(* ---------------- scope resolution ---------------- *)

module S = Sce_core.Ast
module C = Core_lambdae.Ast

(* Names are resolved on the λSCE side now: Sugar produces a named λSCE term
   and Debruijn turns each name into the index of the slot it denotes. These
   tests are about what came out of the second pass. *)
let resolve_exn src =
  let _, named = Sugar.desugar_program (Adt.expand (parse_exn src)) in
  Sce_core.Debruijn.resolve named

let scope_error src =
  match resolve_exn src with
  | _ -> None
  | exception Sugar.Error (msg, _) -> Some msg

(* Top-level declarations chain with `Letb`, so declaration k's value sits under
   k of them and the program's own body follows all of them. *)
let rec bound_at k (t : S.nameless) =
  match (t, k) with
  | S.Letb (_, e1, _, _), 0 -> e1
  | S.Letb (_, _, _, e2), _ -> bound_at (k - 1) e2
  | _ -> failwith "no such top-level declaration"

let rec body_after k (t : S.nameless) =
  if k = 0 then t
  else
    match t with
    | S.Letb (_, _, _, e2) -> body_after (k - 1) e2
    | _ -> failwith "no such top-level declaration"

let rec main_value (t : S.nameless) =
  match t with
  | S.Letb ("main", e1, _, _) -> e1
  | S.Letb (_, _, _, e2) -> main_value e2
  | _ -> failwith "no main"

(* The expression an inner `let ... in` binds. *)
let letb_value = function
  | S.Letb (_, e1, _, _) -> e1
  | _ -> failwith "not a let"

(* λSCE has no variables, so a resolved name is a context projection: a slot
   directly, or a label of one. *)
type occ = Idx of int | Field of int * string

(* Follow a chain of constructors down to the single occurrence a test cares
   about, so the assertions read as "this name resolves to that slot". *)
let rec find_var (e : S.nameless) : occ option =
  match e with
  | S.Proj (S.Query, i) -> Some (Idx i)
  | S.Rproj (S.Proj (S.Query, i), l) -> Some (Field (i, l))
  | S.Lam (_, _, b) | S.Mfunctor (_, _, _, b) | S.Mstruct (_, b)
  | S.Flam (_, _, _, _, b) | S.Inl (_, b) | S.Inr (_, b) | S.Fold (_, b)
  | S.Unfold b | S.Lrec (_, b) | S.Proj (b, _) | S.Rproj (b, _)
  | S.Letb (_, _, _, b) | S.Openm (_, _, b) | S.Box (_, b) ->
    find_var b
  | S.App (a, b) | S.Mapp (a, b) -> (
    match find_var a with Some p -> Some p | None -> find_var b)
  | S.Mrg (_, a, b) | S.Nmrg (a, b) | S.Binop (_, a, b) | S.Mlink (a, b)
  | S.Mlinkn (a, b) -> (
    match find_var b with Some p -> Some p | None -> find_var a)
  | S.If (_, t, _) -> find_var t
  | S.Case (_, _, b, _, _) -> find_var b
  | _ -> None

let test_scoping () =
  print_endline "-- scope resolution --";
  let var name src expected =
    check name (find_var (main_value (resolve_exn src)) = Some expected)
  in

  (* plain binders *)
  var "lambda parameter is index 0" "let main = fun (x : Int) -> x" (Idx 0);
  var "outer lambda parameter is index 1" "let main = fun (x : Int) (y : Int) -> x"
    (Idx 1);
  var "inner lambda parameter is index 0" "let main = fun (x : Int) (y : Int) -> y"
    (Idx 0);
  var "let binds at index 0" "let main = let x = 1 in x" (Idx 0);
  var "shadowing takes the innermost" "let main = let x = 1 in let x = 2 in x" (Idx 0);
  var "earlier let is index 1" "let main = let x = 1 in let y = 2 in x" (Idx 1);
  var "case binder is index 0"
    {|let main = case (inl 1 : Int | String) of inl n -> n | inr s -> 0 end|}
    (Idx 0);

  (* Flam pushes the function itself, then the argument, so inside the bound
     expression the parameters sit below the recursive name. *)
  let bound name src expected =
    check name (find_var (letb_value (main_value (resolve_exn src))) = Some expected)
  in
  bound "let rec: parameter is index 0"
    "let main = let rec f (n : Int) : Int = n in 0" (Idx 0);
  bound "let rec: the recursive name is index 1"
    "let main = let rec f (n : Int) : Int = f n in 0" (Idx 1);
  bound "let rec: two parameters, second is index 0"
    "let main = let rec f (x : Int) (y : Int) : Int = y in 0" (Idx 0);
  bound "let rec: two parameters, first is index 1"
    "let main = let rec f (x : Int) (y : Int) : Int = x in 0" (Idx 1);
  bound "let rec: two parameters, the recursive name is index 2"
    "let main = let rec f (x : Int) (y : Int) : Int = f x y in 0" (Idx 2);
  bound "non-recursive let does not bind its own name in the body"
    "let main = let g (x : Int) : Int = x in 0" (Idx 0);

  (* a struct is one widening frame, not one frame per declaration *)
  check "struct: a later field sees an earlier one at index 0"
    (find_var
       (bound_at 0
          (resolve_exn "module M = struct\n\
                        let a : Int = 1\n\
                        let b : Int = a\n\
                        end"))
     = Some (Field (0, "a")));
  check "struct: the third field still sees the first at index 0"
    (find_var
       (bound_at 0
          (resolve_exn "module M = struct\n\
                        let a : Int = 1\n\
                        let b : Int = 2\n\
                        let c : Int = a\n\
                        end"))
     = Some (Field (0, "a")));

  (* dependent vs non-dependent merge *)
  var "dependent merge exposes the left operand" "let main = { a = 1 } ;; { b = a }"
    (Field (0, "a"));
  check "non-dependent merge does not"
    (scope_error "let main = { a = 1 } ; { b = a }" <> None);

  (* open *)
  var "open brings fields into scope" "let main = open { a = 1 } in a" (Field (0, "a"));
  var "a binding survives an open" "let main = let z = 1 in open { a = 2 } in z"
    (Idx 1);
  var "open of a functor parameter uses its signature"
    "let main = functor (X : { a : Int }) -> open X in a" (Field (0, "a"));
  check "open of an opaque expression is rejected"
    (match scope_error "let main = open (fun (x : Int) -> x) in a" with
     | Some m -> String.starts_with ~prefix:"cannot determine the fields" m
     | None -> false);

  (* sandboxing genuinely cuts the outer context *)
  check "sandbox struct cannot see an outer binding"
    (scope_error "let main = let z = 1 in sandbox struct let w : Int = z end" <> None);
  check "plain struct can see an outer binding"
    (scope_error "let main = let z = 1 in struct let w : Int = z end" = None);
  check "sandbox functor cannot see an outer binding"
    (scope_error "let main = let z = 1 in sandbox functor (X : Top) -> z" <> None);

  (* top-level declarations chain with Letb *)
  check "top level: a later declaration sees an earlier one"
    (find_var (bound_at 1 (resolve_exn "let a : Int = 1\nlet b : Int = a\nlet main = b"))
     = Some (Idx 0));
  var "top level: main sees the last declaration at index 0"
    "let a : Int = 1\nlet b : Int = 2\nlet main = b" (Idx 0);
  var "top level: main sees an earlier declaration at index 1"
    "let a : Int = 1\nlet b : Int = 2\nlet main = a" (Idx 1);
  check "a program with no main returns a record of its bindings"
    (match body_after 2 (resolve_exn "let a : Int = 1\nlet b : Int = 2") with
     | S.Nmrg (S.Lrec ("a", _), S.Lrec ("b", _)) -> true
     | _ -> false);

  (* type variables: mu binders become de Bruijn indices and aliases are
     expanded, both while desugaring *)
  let styp src = Sce.Sepcomp.parse_typ_exn ~what:"test" src in
  check "mu binds its variable to index 0" (styp "mu a. a" = S.TMu (S.TVar 0));
  check "nested mu: the outer binder is index 1"
    (styp "mu a. mu b. a" = S.TMu (S.TMu (S.TVar 1)));
  check "nested mu: the inner binder is index 0"
    (styp "mu a. mu b. b" = S.TMu (S.TMu (S.TVar 0)));
  check "a type alias is expanded" (styp "type A = Int\ntype B = A\nB" = S.TInt);
  check "an unbound type name is rejected" (scope_error "type T = Nope" <> None);

  (* duplicate labels *)
  check "duplicate record labels are rejected"
    (scope_error "let main = { a = 1, a = 2 }" <> None);
  check "duplicate struct fields are rejected"
    (scope_error "module M = struct let a : Int = 1 let a : Int = 2 end" <> None);
  check "duplicate record type labels are rejected"
    (scope_error "type T = { a : Int, a : Int }" <> None);

  check "an unbound variable is rejected" (scope_error "let main = nope" <> None)

(* ---------------- end to end ---------------- *)

(* The two calculi have distinct value types, so compare their first-order
   fragment structurally. Closures are opaque on both sides. *)
let rec same_value (s : S.nameless) (c : C.exp) =
  match (s, c) with
  | S.Lit (S.Int a), C.Lit (C.Int b) -> a = b
  | S.Lit (S.Bool a), C.Lit (C.Bool b) -> a = b
  | S.Lit (S.String a), C.Lit (C.String b) -> String.equal a b
  | S.Unit, C.Unit -> true
  | S.Lrec (l1, v1), C.Lrec (l2, v2) -> String.equal l1 l2 && same_value v1 v2
  | S.Mrg (_, a1, b1), C.Mrg (a2, b2) -> same_value a1 a2 && same_value b1 b2
  | S.Inl (_, v1), C.Inl (_, v2) | S.Inr (_, v1), C.Inr (_, v2) -> same_value v1 v2
  | S.Fold (_, v1), C.Fold (_, v2) -> same_value v1 v2
  | (S.Clos _ | S.Mclos _ | S.Fclos _), (C.Clos _ | C.Fclos _) -> true
  | _ -> false

let test_end_to_end () =
  print_endline "-- end to end --";
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
  in
  ok "integer literal" "let main = 42" "Int" "42";
  ok "arithmetic" "let main = 1 + 2 * 3 - 4" "Int" "3";
  ok "division" "let main = 7 / 2" "Int" "3";
  ok "modulo" "let main = 7 mod 2" "Int" "1";
  ok "unary minus" "let main = 0 - 5" "Int" "-5";
  ok "comparison" "let main = 2 <= 2" "Bool" "true";
  ok "equality on strings" {|let main = "a" = "a"|} "Bool" "true";
  ok "short-circuit and" "let main = false && true" "Bool" "false";
  ok "short-circuit or" "let main = true || false" "Bool" "true";
  ok "negation" "let main = not true" "Bool" "false";
  ok "concatenation" {|let main = "ab" ^ "cd"|} "String" {|"abcd"|};
  ok "unit" "let main = ()" "Top" "()";
  ok "conditional" "let main = if 1 < 2 then 10 else 20" "Int" "10";
  ok "empty record" "let main = {}" "Top" "()";
  ok "record and projection" "let main = { a = 1, b = 2 }.b" "Int" "2";
  ok "record value" "let main = { a = 1, b = 2 }" "{a : Int} & {b : Int}"
    "{ a = 1, b = 2 }";
  ok "application" "let f (x : Int) : Int = x * 2 let main = f 21" "Int" "42";
  ok "curried application"
    "let f (x : Int) (y : Int) : Int = x + y let main = f 1 2" "Int" "3";
  ok "let" "let main = let x = 1 in x + 1" "Int" "2";
  ok "let rec"
    "let main = let rec fact (n : Int) : Int = if n <= 1 then 1 else n * fact (n - 1) \
     in fact 5" "Int" "120";
  ok "non-dependent merge" "let main = { a = 1 } ; { b = 2 }"
    "{a : Int} & {b : Int}" "{ a = 1, b = 2 }";
  ok "dependent merge" "let main = { a = 1 } ;; { b = a + 1 }"
    "{a : Int} & {b : Int}" "{ a = 1, b = 2 }";
  ok "injection" {|let main = (inl 1 : Int | String)|} "Int | String" "inl 1";
  ok "case"
    {|let main = case (inr "hi" : Int | String) of inl n -> "num" | inr s -> s end|}
    "String" {|"hi"|};
  ok "fold and unfold"
    "type N = mu a. Top | a\n\
     let main = case unfold ((fold (inl () : Top | N) : mu a. Top | a)) of inl u -> \
     true | inr m -> false end"
    "Bool" "true";
  ok "structure" "module M = struct let a : Int = 2 let b : Int = a * 3 end let main = M.b"
    "Int" "6";
  ok "sandboxed structure"
    "module M = sandbox struct let k : Int = 42 end let main = M.k" "Int" "42";
  ok "functor application"
    "module F (X : { a : Int }) = struct let b : Int = X.a + 1 end\n\
     module A = F({ a = 1 })\n\
     let main = A.b" "Int" "2";
  ok "link"
    "module C = struct let start : Int = 1 end\n\
     module L = link C with functor (X : { start : Int }) -> struct let next : \
     Int = X.start + 1 end\n\
     let main = L.next" "Int" "2";
  ok "linkall"
    "module P = struct let w : Int = 3 let h : Int = 4 end\n\
     module A = linkall P with functor (X : { w : Int } & { h : Int }) -> \
     struct let area : Int = X.w * X.h end\n\
     let main = A.area" "Int" "12";
  ok "open expression" "let main = open { a = 1, b = 2 } in a + b" "Int" "3";
  ok "open declaration"
    "module M = struct let a : Int = 41 end\nopen M\nlet main = a + 1" "Int" "42";
  ok "type alias" "type T = Int\nlet main = (1 : T)" "Int" "1";
  ok "program without a main" "let a : Int = 1\nlet b : Int = 2"
    "{a : Int} & {b : Int}" "{ a = 1, b = 2 }";
  ok "query escape hatch" "let main = let x = 7 in ?.[0]" "Int" "7";
  ok "adt construction and match"
    "type shape = | Circle of Int | Rect of Int * Int | Point\n\
     let area (s : shape) : Int =\n\
    \  match s with\n\
    \  | Circle r -> r * r * 3\n\
    \  | Rect (w, h) -> w * h\n\
    \  | Point -> 0\n\
    \  end\n\
     let main = area (Rect (4, 5))" "Int" "20";
  ok "adt recursion"
    "type expr = | Lit of Int | Add of expr * expr\n\
     let rec eval (e : expr) : Int =\n\
    \  match e with | Lit n -> n | Add (a, b) -> eval a + eval b end\n\
     let main = eval (Add (Add (Lit 1, Lit 2), Lit 39))" "Int" "42";
  ok "adt wildcard" "type c = | R | G | B\nlet main = match G with | R -> 1 | _ -> 2 end"
    "Int" "2";
  ok "adt payload record binding"
    "type p = | P of Int * Int\n\
     let main = match P (3, 4) with P q -> q._1 * q._2 end" "Int" "12";
  ok "tuple projection" "let main = (7, 8)._2" "Int" "8"

let test_differential () =
  print_endline "-- differential --";
  let programs =
    [
      "let main = 1 + 2 * 3";
      "let main = { a = 1, b = 2 }";
      "let main = let rec f (n : Int) : Int = if n <= 1 then 1 else n * f (n - 1) in f 5";
      {|let main = (inl 1 : Int | String)|};
      "let main = { a = 1 } ;; { b = a + 1 }";
      "module M = struct let a : Int = 2 let b : Int = a * 3 end let main = M.b";
      "module M = sandbox struct let k : Int = 42 end let main = M.k";
      "module C = struct let s : Int = 1 end\n\
       module L = link C with functor (X : { s : Int }) -> struct let n : Int = \
       X.s + 1 end\n\
       let main = L.n";
      "let main = open { a = 1, b = 2 } in a + b";
      "type e = | L of Int | N of e * e\n\
       let rec s (x : e) : Int =\n\
       \  match x with | L n -> n | N (a, b) -> s a + s b end\n\
       let main = s (N (L 1, N (L 2, L 3)))";
    ]
  in
  List.iteri
    (fun i src ->
      match Sce.Pipeline.run src with
      | Error e ->
        check (Printf.sprintf "differential %d: runs" i) false;
        print_endline (Sce.Pipeline.render ~src e)
      | Ok o ->
        (* λSCE evaluation agrees with λE evaluation of its elaboration *)
        let sv = Sce_core.Eval.eval S.Unit o.sce_exp in
        check
          (Printf.sprintf "differential %d: λSCE and λE agree" i)
          (same_value sv o.value);
        (* big-step agrees with small-step *)
        let small = Core_lambdae.Eval.eval' C.Unit o.core_exp in
        check
          (Printf.sprintf "differential %d: big-step and small-step agree" i)
          (Core_lambdae.Pretty.exp_to_string small
          = Core_lambdae.Pretty.exp_to_string o.value);
        (* λSCE small-step agrees with λSCE big-step *)
        let s_small = Sce_core.Eval.eval' S.Unit o.sce_exp in
        check
          (Printf.sprintf "differential %d: λSCE big-step and small-step agree" i)
          (same_value s_small o.value))
    programs

let test_failures () =
  print_endline "-- rejected programs --";
  let rejects name src stage line col =
    match Sce.Pipeline.run src with
    | Ok _ -> check name false
    | Error e ->
      if e.stage = stage && e.line = line && e.col = col then check name true
      else (
        check name false;
        Printf.printf "        expected %s at %d:%d, got %s at %d:%d — %s\n"
          stage line col e.stage e.line e.col e.message)
  in
  (* Sugar rejects what would make the translation meaningless — an unbound
     name, or a type whose shape it cannot continue from. Everything else is a
     type error, which Elab raises on the term Sugar built. *)
  rejects "unbound variable" "let main = nope" "desugar" 1 11;
  rejects "unbound type name" "type T = Nope\nlet main = 1" "desugar" 1 9;
  rejects "duplicate record labels" "let main = { a = 1, a = 2 }" "desugar" 1 11;
  rejects "duplicate structure fields"
    "module M = struct let a : Int = 1 let a : Int = 2 end let main = 1" "desugar" 1 34;
  rejects "open of an opaque expression"
    "let main = open (fun (x : Int) -> x) in a" "desugar" 1 16;
  rejects "sandbox hides the outer context"
    "let main = let z = 1 in sandbox struct let w : Int = z end" "desugar" 1 53;
  rejects "annotation mismatch" "let main = (1 : String)" "elaborate" 1 0;
  rejects "argument mismatch"
    {|let f (x : Int) : Int = x let main = f "s"|} "elaborate" 1 0;
  rejects "application of a non-function" "let main = 1 2" "desugar" 1 11;
  rejects "case on a non-union" "let main = case 1 of inl a -> 1 | inr b -> 2 end"
    "desugar" 1 16;
  rejects "if branches disagree" {|let main = if true then 1 else "s"|} "elaborate" 1 0;
  rejects "case branches disagree"
    {|let main = case (inl 1 : Int | String) of inl n -> n | inr s -> s end|}
    "elaborate" 1 0;
  rejects "let rec without a return annotation"
    "let main = let rec f (n : Int) = n in 1" "desugar" 1 19;
  rejects "unascribed injection" "let main = inl 1" "desugar" 1 11;
  rejects "unascribed fold" "let main = fold 1" "desugar" 1 11;
  rejects "unfold of a non-recursive type" "let main = unfold 1" "desugar" 1 18;
  rejects "link against a non-functor" "let main = link { a = 1 } with 1" "desugar" 1 11;
  rejects "link with an unsatisfied import"
    "let main = link { a = 1 } with functor (X : { b : Int }) -> X" "elaborate" 1 0;
  rejects "division by zero" "let main = 1 / 0" "runtime" 1 0;
  rejects "syntax error" "let main = 1 +" "parse" 1 14;
  (* Applying a wider module directly is rejected: the calculus has no
     subtyping, which is what `link` exists to work around. *)
  rejects "no subtyping on functor application"
    "module M = struct let a : Int = 1 let b : Int = 2 end\n\
     module F (X : { a : Int }) = struct let c : Int = X.a end\n\
     module A = F(M)\n\
     let main = 1" "elaborate" 1 0;
  rejects "non-exhaustive match" "type c = | R | G\nlet main = match R with | R -> 1 end"
    "adt" 2 11;
  rejects "unknown constructor in a pattern"
    "type c = | R | G\nlet main = match R with | R -> 1 | B -> 2 end" "adt" 2 35;
  rejects "duplicate match arm"
    "type c = | R | G\nlet main = match R with | R -> 1 | R -> 2 | G -> 3 end" "adt" 2 35;
  rejects "unreachable wildcard arm"
    "type c = | R | G\nlet main = match R with | R -> 1 | G -> 2 | _ -> 3 end" "adt" 2 11;
  rejects "constructor used without its payload" "type s = | K of Int\nlet main = K"
    "adt" 2 11;
  rejects "duplicate constructor" "type c = | R | R\nlet main = 1" "adt" 1 15;
  rejects "match on a non-adt value"
    "type c = | R | G\nlet f (x : Int) : Int = x\n\
     let main = match f 1 with | R -> 1 | G -> 2 end" "elaborate" 1 0;
  rejects "wrong tuple payload arity"
    "type s = | K of Int * Int\nlet main = K (1, 2, 3)" "elaborate" 1 0

let test_examples () =
  print_endline "-- examples --";
  let dir = "../examples" in
  let files = Sys.readdir dir in
  Array.sort compare files;
  Array.iter
    (fun f ->
      if Filename.check_suffix f ".sce" then begin
        let path = Filename.concat dir f in
        let ic = open_in_bin path in
        let src = really_input_string ic (in_channel_length ic) in
        close_in ic;
        match Sce.Pipeline.run src with
        | Ok _ -> check ("runs: " ^ f) true
        | Error e ->
          check ("runs: " ^ f) false;
          print_endline (Sce.Pipeline.render ~src e)
      end)
    files;
  (* recursive linking as a derived form: the knot must close, with the value
     the mechanization's Theorem 31 predicts *)
  let path = Filename.concat dir "linkrec/parity.sce" in
  let ic = open_in_bin path in
  let src = really_input_string ic (in_channel_length ic) in
  close_in ic;
  (match Sce.Pipeline.run src with
   | Ok o ->
     check "runs: linkrec/parity.sce"
       (Sce.Pipeline.value_string o
        = "{ even10 = true, odd10 = false, even7 = false }")
   | Error e ->
     check "runs: linkrec/parity.sce" false;
     print_endline (Sce.Pipeline.render ~src e))

let () =
  test_parsing ();
  print_newline ();
  test_scoping ();
  print_newline ();
  test_end_to_end ();
  print_newline ();
  test_differential ();
  print_newline ();
  test_failures ();
  print_newline ();
  test_examples ();
  print_newline ();
  if !failures = 0 then print_endline "all tests passed"
  else (
    Printf.printf "%d test(s) failed\n" !failures;
    exit 1)
