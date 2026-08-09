(* Evaluation for λE. *)
open Ast

(* type exp =
  (* unions: Inl (B, e) injects into _ ∨ B, Inr (A, e) into A ∨ _ *)
  | Inl   of typ * exp
  | Inr   of typ * exp
  | Case  of exp * exp * exp
  (* fixpoint: Flam (A, B, e) is a recursive function of type A → B;
     its body sees ?.0 = argument, ?.1 = the function itself *)
  | Flam  of typ * typ * exp
  | Fclos of exp * typ * typ * exp
  (* iso-recursive types: Fold (T, e) stores the mu-body T, folds into mu T *)
  | Fold    of typ * exp
  | Unfold  of exp *)

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

(* Interpreter based on big-step semantics. *)
let rec eval (env : exp) (e : exp) : exp =
  match e with
  | Lit _ | Unit | Clos _ -> e
  | Mrg (e1, e2) ->
    let v1 = eval env e1 in
    Mrg (v1, eval (Mrg (env, v1)) e2)
  | Lam (ty, body) -> Clos (env, ty, body)
  | Box (e1, e2) ->
    let env' = eval env e1 in
    eval env' e2
  | App (e1, e2) ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    begin match v1 with
      | Clos (cenv, _ty, body) -> eval (Mrg (cenv, v2)) body
      | _ -> failwith "Error: Application (e1 e2) must have e1 as closure."
    end
  | Proj (e1, i) -> lookup (eval env e1) i
  | Lrec (l, e1) -> Lrec (l, eval env e1)
  | Rproj (e1, l) -> rlookup (eval env e1) l
  | Query -> env
  | _ -> failwith "TODO"

(* Interpreter based on small-step semantics. *)
let rec step (env : exp) (e : exp) : exp =
  match e with
  | Lit _ | Unit -> e
  | Mrg (e1, e2) ->
    if is_value e1 then Mrg (e1, step (Mrg (env, e1)) e2)
    else env
  | Query -> env
  | _ -> failwith "TODO"

(* Driver for small-step based interpreter. *)
let rec eval' (env : exp) (e : exp) : exp =
  if is_value e then e else eval' env (step env e)
 