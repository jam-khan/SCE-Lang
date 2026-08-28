(* Evaluation for λSCE. *)
open Ast

(* LookupV: index 0 is the *right-most* component of a merge. *)
let rec lookup (v : nameless) (i : int) : nameless =
  match v with
  | Mrg (_, v1, v2) | Nmrg (v1, v2) ->
    if i = 0 then v2 else lookup v1 (i - 1)
  | _ -> failwith ("Error: no component at index " ^ string_of_int i)

(* Sel with option response *)
let rec sel_opt (v : nameless) (l : string) : nameless option =
  match v with
  | Lrec (l', v') when String.equal l l' -> Some v'
  | Mrg (_, v1, v2) | Nmrg (v1, v2) ->
    (match sel_opt v2 l with
     | Some _ as r -> r
     | None -> sel_opt v1 l)
  | _ -> None

(* Sel: label `l` selection in `v` *)
let sel (v : nameless) (l : string) : nameless =
  match sel_opt v l with
  | Some v' -> v'
  | None -> failwith ("Error: no field labelled " ^ l)

(* SelPkg: build the record package for the import interface `d` out of `v`. *)
let rec selpkg (v : nameless) (d : typ) : nameless =
  match d with
  | TRcd (l, _) -> Lrec (l, sel v l)
  | TAnd (d', TRcd (l, _)) -> Mrg (anon, selpkg v d', Lrec (l, sel v l))
  | _ -> failwith "Error: import interface must be a record or intersection of records."

(* Prim: apply a primitive operator to two literal operands. *)
let prim (op : binop) (l1 : lit) (l2 : lit) : lit =
  let nonzero n =
    if n = 0 then failwith "Error: division by zero" else n
  in
  match op, l1, l2 with
  | Add, Int a, Int b -> Int (a + b)
  | Sub, Int a, Int b -> Int (a - b)
  | Mul, Int a, Int b -> Int (a * b)
  | Div, Int a, Int b -> Int (a / nonzero b)
  | Mod, Int a, Int b -> Int (a mod nonzero b)
  | Lt,  Int a, Int b -> Bool (a < b)
  | Le,  Int a, Int b -> Bool (a <= b)
  | Gt,  Int a, Int b -> Bool (a > b)
  | Ge,  Int a, Int b -> Bool (a >= b)
  | Cat, String a, String b -> String (a ^ b)
  | Eq, _, _ -> Bool (l1 = l2)
  | Ne, _, _ -> Bool (l1 <> l2)
  | _ -> failwith "Error: primitive operator applied to ill-typed operands."

(* Both operands of a primitive reduce to literals; anything else is ill-typed. *)
let prim_exp (op : binop) (v1 : nameless) (v2 : nameless) : nameless =
  match v1, v2 with
  | Lit l1, Lit l2 -> Lit (prim op l1 l2)
  | _ -> failwith "Error: primitive operator applied to non-literals."

let branch (v : nameless) (e2 : nameless) (e3 : nameless) : nameless =
  match v with
  | Lit (Bool true)  -> e2
  | Lit (Bool false) -> e3
  | _ -> failwith "Error: if condition must evaluate to a boolean."

(* Interpreter based on big-step semantics. *)
let rec eval (env : nameless) (e : nameless) : nameless =
  match e with
  | Var _ -> .
  | Lit _ | Unit | Clos _ | Mclos _ | Fclos _ -> e
  | Query -> env
  | Lam (_, ty, body) -> Clos (env, ty, body)
  | Flam (_, _, tyA, tyB, body) -> Fclos (env, tyA, tyB, body)
  | Box (e1, e2) ->
    let env' = eval env e1 in
    eval env' e2
  | Mrg (x, e1, e2) ->
    let v1 = eval env e1 in
    Mrg (x, v1, eval (Mrg (x, env, v1)) e2)
  | Nmrg (e1, e2) ->
    let v1 = eval env e1 in
    Mrg (anon, v1, eval env e2)
  | App (e1, e2) ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    begin match v1 with
      | Clos (cenv, _ty, body) -> eval (Mrg (anon, cenv, v2)) body
      | Fclos (cenv, _tyA, _tyB, body) ->
        eval (Mrg (anon, Mrg (anon, cenv, v1), v2)) body
      | _ -> failwith "Error: Application (e1 e2) must have e1 as closure."
    end
  | Mapp (e1, e2) ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    begin match v1 with
      | Mclos (cenv, _ty, body) -> eval (Mrg (anon, cenv, v2)) body
      | _ -> failwith "Error: Module application (e1 e2) must have e1 as module closure."
    end
  | Proj (e1, i) -> lookup (eval env e1) i
  | Lrec (l, e1) -> Lrec (l, eval env e1)
  | Rproj (e1, l) -> sel (eval env e1) l
  | Binop (op, e1, e2) ->
    (* left to right, explicitly: OCaml applies arguments right to left *)
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    prim_exp op v1 v2
  | If (e1, e2, e3) -> eval env (branch (eval env e1) e2 e3)
  | Letb (x, e1, _ty, e2) ->
    let v1 = eval env e1 in
    eval (Mrg (x, env, v1)) e2
  | Openm (x, e1, e2) ->
    begin match eval env e1 with
      | Lrec (_l, v') -> eval (Mrg (x, env, v')) e2
      | _ -> failwith "Error: Open must have a labelled record as its subject."
    end
  | Mstruct (Sandboxed, body) -> eval Unit body
  | Mstruct (Open, body) -> eval env body
  | Mfunctor (Sandboxed, _, ty, body) -> Mclos (Unit, ty, body)
  | Mfunctor (Open, _, ty, body) -> Mclos (env, ty, body)
  | Mlink (e1, e2) ->
    let v1 = eval env e1 in
    begin match eval env e2 with
      | Mclos (cenv, TRcd (l, _), body) ->
        let vl = sel v1 l in
        Mrg (anon, v1, eval (Mrg (anon, cenv, Lrec (l, vl))) body)
      | _ -> failwith "Error: Link must have a module closure with a record import."
    end
  | Mlinkn (e1, e2) ->
    let v1 = eval env e1 in
    begin match eval env e2 with
      | Mclos (cenv, d, body) ->
        let pkg = selpkg v1 d in
        Mrg (anon, v1, eval (Mrg (anon, cenv, pkg)) body)
      | _ -> failwith "Error: N-ary link must have a module closure."
    end
  | Inl (ty, e1) -> Inl (ty, eval env e1)
  | Inr (ty, e1) -> Inr (ty, eval env e1)
  | Case (e1, x, el, y, er) ->
    begin match eval env e1 with
      | Inl (_, v) -> eval (Mrg (x, env, v)) el
      | Inr (_, v) -> eval (Mrg (y, env, v)) er
      | _ -> failwith "Error: Case analysis must evaluate to an injection."
    end
  | Fold (ty, e1) -> Fold (ty, eval env e1)
  | Unfold e1 ->
    begin match eval env e1 with
      | Fold (_, v) -> v
      | _ -> failwith "Error: Unfold applied to a non-fold value."
    end

(* Interpreter based on small-step semantics. *)
let rec step (env : nameless) (e : nameless) : nameless =
  match e with
  | Var _ -> .
  | _ when is_value e -> e
  | Query -> env
  | Lam (_, ty, body) -> Clos (env, ty, body)
  | Flam (_, _, tyA, tyB, body) -> Fclos (env, tyA, tyB, body)
  | Mfunctor (Sandboxed, _, ty, body) -> Mclos (Unit, ty, body)
  | Mfunctor (Open, _, ty, body) -> Mclos (env, ty, body)
  | Box (e1, e2) ->
    if not (is_value e1) then Box (step env e1, e2)
    else if not (is_value e2) then Box (e1, step e1 e2)
    else e2
  | Mrg (x, e1, e2) ->
    if is_value e1 then Mrg (x, e1, step (Mrg (x, env, e1)) e2)
    else Mrg (x, step env e1, e2)
  | Nmrg (e1, e2) ->
    if not (is_value e1) then Nmrg (step env e1, e2)
    else if not (is_value e2) then Nmrg (e1, step env e2)
    else Mrg (anon, e1, e2)
  | App (e1, e2) ->
    if not (is_value e1) then App (step env e1, e2)
    else if not (is_value e2) then App (e1, step env e2)
    else begin match e1 with
      | Clos (cenv, _ty, body) -> Box (Mrg (anon, cenv, e2), body)
      | Fclos (cenv, _tyA, _tyB, body) ->
        Box (Mrg (anon, Mrg (anon, cenv, e1), e2), body)
      | _ -> failwith "Error: Application (e1 e2) must have e1 as closure."
    end
  | Mapp (e1, e2) ->
    if not (is_value e1) then Mapp (step env e1, e2)
    else if not (is_value e2) then Mapp (e1, step env e2)
    else begin match e1 with
      | Mclos (cenv, _ty, body) -> Box (Mrg (anon, cenv, e2), body)
      | _ -> failwith "Error: Module application (e1 e2) must have e1 as module closure."
    end
  | Proj (e1, i) ->
    if is_value e1 then lookup e1 i else Proj (step env e1, i)
  | Lrec (l, e1) -> Lrec (l, step env e1)
  | Rproj (e1, l) ->
    if is_value e1 then sel e1 l else Rproj (step env e1, l)
  | Binop (op, e1, e2) ->
    if not (is_value e1) then Binop (op, step env e1, e2)
    else if not (is_value e2) then Binop (op, e1, step env e2)
    else prim_exp op e1 e2
  | If (e1, e2, e3) ->
    if is_value e1 then branch e1 e2 e3 else If (step env e1, e2, e3)
  | Letb (x, e1, ty, e2) ->
    if is_value e1 then Box (Mrg (x, env, e1), e2)
    else Letb (x, step env e1, ty, e2)
  | Openm (x, e1, e2) ->
    if not (is_value e1) then Openm (x, step env e1, e2)
    else begin match e1 with
      | Lrec (_l, v') -> Box (Mrg (x, env, v'), e2)
      | _ -> failwith "Error: Open must have a labelled record as its subject."
    end
  | Mstruct (Sandboxed, e1) ->
    if is_value e1 then e1 else Mstruct (Sandboxed, step Unit e1)
  | Mstruct (Open, e1) ->
    if is_value e1 then e1 else Mstruct (Open, step env e1)
  | Mlink (e1, e2) ->
    if not (is_value e1) then Mlink (step env e1, e2)
    else if not (is_value e2) then Mlink (e1, step env e2)
    else begin match e2 with
      | Mclos (cenv, TRcd (l, _), body) ->
        let vl = sel e1 l in
        Mrg (anon, e1, Box (Mrg (anon, cenv, Lrec (l, vl)), body))
      | _ -> failwith "Error: Link must have a module closure with a record import."
    end
  | Mlinkn (e1, e2) ->
    if not (is_value e1) then Mlinkn (step env e1, e2)
    else if not (is_value e2) then Mlinkn (e1, step env e2)
    else begin match e2 with
      | Mclos (cenv, d, body) ->
        let pkg = selpkg e1 d in
        Mrg (anon, e1, Box (Mrg (anon, cenv, pkg), body))
      | _ -> failwith "Error: N-ary link must have a module closure."
    end
  | Inl (ty, e1) -> Inl (ty, step env e1)
  | Inr (ty, e1) -> Inr (ty, step env e1)
  | Case (e1, x, el, y, er) ->
    if not (is_value e1) then Case (step env e1, x, el, y, er)
    else begin match e1 with
      | Inl (_, v) -> Box (Mrg (x, env, v), el)
      | Inr (_, v) -> Box (Mrg (y, env, v), er)
      | _ -> failwith "Error: Case analysis must evaluate to an injection."
    end
  | Fold (ty, e1) -> Fold (ty, step env e1)
  | Unfold e1 ->
    if not (is_value e1) then Unfold (step env e1)
    else begin match e1 with
      | Fold (_, v) -> v
      | _ -> failwith "Error: Unfold applied to a non-fold value."
    end
  | Lit _ | Unit | Clos _ | Mclos _ | Fclos _ -> e

(* Driver for small-step based interpreter. *)
let rec eval' (env : nameless) (e : nameless) : nameless =
  if is_value e then e else eval' env (step env e)