(* Evaluation for λE. *)
open Ast

(* Host capabilities: `Hostfn` values apply through this dispatcher, which the
   embedding layer installs (lib/units/host.ml). The core stays closed — with no
   dispatcher installed, every capability application fails. *)
let host_dispatch : (string -> (exp -> exp) option) ref = ref (fun _ -> None)

let host_apply (name : string) (v : exp) : exp =
  match !host_dispatch name with
  | Some f -> f v
  | None -> failwith ("Error: no host capability named " ^ name)

(* lookupV: index is the *right-most* component of `v`. *)
let rec lookup (v : exp) (i : int) : exp =
  match v with
  | Mrg (v1, v2) -> if i = 0 then v2 else lookup v1 (i - 1)
  | _ -> failwith ("Error: no component at index " ^ string_of_int i)

(* rlookup with option response *)
let rec rlookup_opt (v : exp) (l : string) : exp option =
  match v with
  | Lrec (l', v') when String.equal l l' -> Some v'
  | Mrg (v1, v2) ->
    (match rlookup_opt v2 l with
     | Some _ as r -> r
     | None -> rlookup_opt v1 l)
  | _ -> None

(* RLookupV: label `l` lookup in the `v` *)
let rlookup (v : exp) (l : string) : exp =
  match rlookup_opt v l with
  | Some v' -> v'
  | None -> failwith ("Error: no field labelled " ^ l)

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
let prim_exp (op : binop) (v1 : exp) (v2 : exp) : exp =
  match v1, v2 with
  | Lit l1, Lit l2 -> Lit (prim op l1 l2)
  | _ -> failwith "Error: primitive operator applied to non-literals."

let branch (v : exp) (e2 : exp) (e3 : exp) : exp =
  match v with
  | Lit (Bool true)  -> e2
  | Lit (Bool false) -> e3
  | _ -> failwith "Error: if condition must evaluate to a boolean."

(* Interpreter based on big-step semantics. *)
let rec eval (env : exp) (e : exp) : exp =
  match e with
  | Mrg (e1, e2)    ->
    let v1 = eval env e1 in
    Mrg (v1, eval (Mrg (env, v1)) e2)
  | Lam (ty, body)  -> Clos (env, ty, body)
  | Box (e1, e2)    ->
    let env' = eval env e1 in
    eval env' e2
  | App (e1, e2)    ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    begin match v1 with
      | Clos (cenv, _ty, body)          -> 
        eval (Mrg (cenv, v2)) body
      | Fclos (cenv, _tyA, _tyB, body)  ->
        eval (Mrg (Mrg (cenv, v1), v2)) body
      | Hostfn (name, _, _)             -> host_apply name v2
      | _ -> failwith "Error: Application (e1 e2) must have e1 as closure."
    end
  | Proj (e1, i)  -> lookup (eval env e1) i
  | Lrec (l, e1)  -> Lrec (l, eval env e1)
  | Rproj (e1, l) -> rlookup (eval env e1) l
  | Query         -> env
  | Binop (op, e1, e2) ->
    (* left to right, explicitly: OCaml applies arguments right to left *)
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    prim_exp op v1 v2
  | If (e1, e2, e3)    -> eval env (branch (eval env e1) e2 e3)
  | Inl (ty, e1)  -> Inl (ty, eval env e1)
  | Inr (ty, e1)  -> Inr (ty, eval env e1)  
  | Case (e1, el, er) ->
    begin match eval env e1 with
      | Inl (_, v)  -> eval (Mrg (env, v)) el
      | Inr (_, v)  -> eval (Mrg (env, v)) er
      | _           -> failwith "Error: Case analysis must evaluate to an injection."
    end
  | Flam (tyA, tyB, e) -> Fclos (env, tyA, tyB, e)
  | Fold (ty, e1)      -> Fold (ty, eval env e1)
  | Unfold e1          ->
    begin match eval env e1 with
      | Fold (_, v) -> v
      | _ -> failwith "Error: Unfold applied to a non-fold value."  
    end
  | Lit _ | Unit | Clos _ | Fclos _ | Hostfn _ -> e

(* Interpreter based on small-step semantics. *)
let rec step (env : exp) (e : exp) : exp =
  match e with
  | _ when is_value e -> e
  | Query -> env
  | Lam (ty, body) -> Clos (env, ty, body)
  | Flam (tyA, tyB, body) -> Fclos (env, tyA, tyB, body)
  | Mrg (e1, e2) ->
    if is_value e1 then Mrg (e1, step (Mrg (env, e1)) e2)
    else Mrg (step env e1, e2)
  | App (e1, e2) ->
    if not (is_value e1) then App (step env e1, e2)
    else if not (is_value e2) then App (e1, step env e2)
    else begin match e1 with
      | Clos (cenv, _ty, body) -> Box (Mrg (cenv, e2), body)
      | Fclos (cenv, _tyA, _tyB, body) -> Box (Mrg (Mrg (cenv, e1), e2), body)
      | Hostfn (name, _, _) -> host_apply name e2
      | _ -> failwith "Error: Application (e1 e2) must have e1 as closure."
    end
  | Box (e1, e2) ->
    if not (is_value e1) then Box (step env e1, e2)
    else if not (is_value e2) then Box (e1, step e1 e2)
    else e2
  | Proj (e1, i) ->
    if is_value e1 then lookup e1 i else Proj (step env e1, i)
  | Lrec (l, e1) -> Lrec (l, step env e1)
  | Rproj (e1, l) ->
    if is_value e1 then rlookup e1 l else Rproj (step env e1, l)
  | Binop (op, e1, e2) ->
    if not (is_value e1) then Binop (op, step env e1, e2)
    else if not (is_value e2) then Binop (op, e1, step env e2)
    else prim_exp op e1 e2
  | If (e1, e2, e3) ->
    if is_value e1 then branch e1 e2 e3 else If (step env e1, e2, e3)
  | Inl (ty, e1) -> Inl (ty, step env e1)
  | Inr (ty, e1) -> Inr (ty, step env e1)
  | Case (e1, el, er) ->
    if not (is_value e1) then Case (step env e1, el, er)
    else begin match e1 with
      | Inl (_, v) -> Box (Mrg (env, v), el)
      | Inr (_, v) -> Box (Mrg (env, v), er)
      | _ -> failwith "Error: Case analysis must evaluate to an injection."
    end
  | Fold (ty, e1) -> Fold (ty, step env e1)
  | Unfold e1 ->
    if not (is_value e1) then Unfold (step env e1)
    else begin match e1 with
      | Fold (_, v) -> v
      | _ -> failwith "Error: Unfold applied to a non-fold value."
    end
  | Lit _ | Unit | Clos _ | Fclos _ | Hostfn _ -> e

(* Driver for small-step based interpreter. *)
let rec eval' (env : exp) (e : exp) : exp =
  if is_value e then e else eval' env (step env e)
 