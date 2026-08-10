(* Type checker for core λE with extensions. *)
open Ast

exception Type_error of string

let type_error msg = raise (Type_error msg)

(* substTyp d S T replaces var d by S in T (S is closed, so no shifting) *)
let rec subst_typ (d : int) (s : typ) (t : typ) : typ =
  match t with
  | TInt | TBool | TString | TTop -> t
  | TArr (a, b) -> TArr (subst_typ d s a, subst_typ d s b)
  | TAnd (a, b) -> TAnd (subst_typ d s a, subst_typ d s b)
  | TOr (a, b) -> TOr (subst_typ d s a, subst_typ d s b)
  | TRcd (l, a) -> TRcd (l, subst_typ d s a)
  | TVar n -> if n = d then s else t
  | TMu t' -> TMu (subst_typ (d + 1) s t')

let unfold_mu (t : typ) : typ = subst_typ 0 (TMu t) t

(* Lookup: index 0 is the *right-most* component of an intersection. *)
let rec tlookup (a : typ) (n : int) : typ =
  match a with
  | TAnd (a1, a2) -> if n = 0 then a2 else tlookup a1 (n - 1)
  | _ -> type_error ("no component at index " ^ string_of_int n)

(* Lin: label `l` occurs somewhere in `a`. *)
let rec lin (l : string) (a : typ) : bool =
  match a with
  | TRcd (l', _) -> String.equal l l'
  | TAnd (a1, a2) -> lin l a1 || lin l a2
  | _ -> false

(* RLookup: unambiguous lookup of label `l` in `a`. *)
let rec rlookup_typ_opt (a : typ) (l : string) : typ option =
  match a with
  | TRcd (l', a') when String.equal l l' -> Some a'
  | TAnd (a1, a2) ->
    if lin l a2 then
      if lin l a1 then None else rlookup_typ_opt a2 l
    else rlookup_typ_opt a1 l
  | _ -> None

let rlookup_typ (a : typ) (l : string) : typ =
  match rlookup_typ_opt a l with
  | Some a' -> a'
  | None -> type_error ("no unambiguous field labelled " ^ l)

let type_of_lit = function
  | Int _ -> TInt
  | Bool _ -> TBool
  | String _ -> TString

(* Operand and result types of each primitive operator. `Eq`/`Ne` are the only
   operators that are not fixed-arity monomorphic, so they are handled apart. *)
let type_of_binop (op : binop) (a : typ) (b : typ) : typ =
  let expect ta tb tr =
    if a = ta && b = tb then tr
    else type_error "operand type mismatch in primitive operation"
  in
  match op with
  | Add | Sub | Mul | Div | Mod -> expect TInt TInt TInt
  | Lt | Le | Gt | Ge -> expect TInt TInt TBool
  | Cat -> expect TString TString TString
  | Eq | Ne ->
    if a = b && (a = TInt || a = TBool || a = TString) then TBool
    else type_error "equality expects two operands of the same primitive type"

(* Type checker based on the `HasType` judgment. *)
let rec infer (ctx : typ) (e : exp) : typ =
  match e with
  | Query -> ctx
  | Lit l -> type_of_lit l
  | Unit -> TTop
  | App (e1, e2) ->
    begin match infer ctx e1 with
      | TArr (a, b) ->
        let a' = infer ctx e2 in
        if a' = a then b else type_error "argument type mismatch"
      | t -> type_error ("application of a non-function: " ^ Pretty.typ_to_string t)
    end
  | Box (e1, e2) ->
    let ctx' = infer ctx e1 in
    infer ctx' e2
  | Mrg (e1, e2) ->
    let a = infer ctx e1 in
    let b = infer (TAnd (ctx, a)) e2 in
    TAnd (a, b)
  | Lam (a, body) -> TArr (a, infer (TAnd (ctx, a)) body)
  | Clos (v, a, body) ->
    if not (is_value v) then type_error "closure environment must be a value";
    let ctx1 = infer TTop v in
    TArr (a, infer (TAnd (ctx1, a)) body)
  | Proj (e1, n) -> tlookup (infer ctx e1) n
  | Lrec (l, e1) -> TRcd (l, infer ctx e1)
  | Rproj (e1, l) -> rlookup_typ (infer ctx e1) l
  | Binop (op, e1, e2) -> type_of_binop op (infer ctx e1) (infer ctx e2)
  | If (e1, e2, e3) ->
    if infer ctx e1 <> TBool then type_error "if condition is not a boolean";
    let a = infer ctx e2 in
    let b = infer ctx e3 in
    if a = b then a else type_error "if branches have different types"
  | Inl (b, e1) -> TOr (infer ctx e1, b)
  | Inr (a, e1) -> TOr (a, infer ctx e1)
  | Case (e1, el, er) ->
    begin match infer ctx e1 with
      | TOr (a, b) ->
        let c1 = infer (TAnd (ctx, a)) el in
        let c2 = infer (TAnd (ctx, b)) er in
        if c1 = c2 then c1 else type_error "case branches have different types"
      | _ -> type_error "case scrutinee is not a union"
    end
  | Flam (a, b, body) ->
    let b' = infer (TAnd (TAnd (ctx, TArr (a, b)), a)) body in
    if b' = b then TArr (a, b)
    else type_error "recursive function body type mismatch"
  | Fclos (v, a, b, body) ->
    if not (is_value v) then type_error "closure environment must be a value";
    let ctx1 = infer TTop v in
    let b' = infer (TAnd (TAnd (ctx1, TArr (a, b)), a)) body in
    if b' = b then TArr (a, b)
    else type_error "recursive function body type mismatch"
  | Fold (t, e1) ->
    let a = infer ctx e1 in
    if a = unfold_mu t then TMu t
    else type_error "fold body does not match unrolled type"
  | Unfold e1 ->
    begin match infer ctx e1 with
      | TMu t -> unfold_mu t
      | _ -> type_error "unfold applied to a non-recursive type"
    end

let typecheck (e : exp) : typ = infer TTop e