(* Elaboration from λSCE to λE. *)
open Ast
module C = Core_lambdae.Ast

exception Elab_error of string

let elab_error msg = raise (Elab_error msg)

(* type-level judgements *)
let unfold_mu (t : typ) : typ = subst_typ 0 (TMu t) t

(* SLookup: index 0 is the *right-most* component of an intersection. *)
let rec slookup (a : typ) (n : int) : typ =
  match a with
  | TAnd (a1, a2) -> if n = 0 then a2 else slookup a1 (n - 1)
  | _ -> elab_error ("no component at index " ^ string_of_int n)

(* LabelIn: label occurs in the type (descends into signature interfaces). *)
  let rec label_in (l : string) (a : typ) : bool =
  match a with
  | TRcd (l', _)    -> String.equal l l'
  | TAnd (a1, a2)   -> label_in l a1 || label_in l a2
  | TSig (TyIntf t) -> label_in l t
  | _               -> false

(* SRLookup: unambiguous record lookup (label present on exactly one side). *)
let rec srlookup_opt (a : typ) (l : string) : typ option =
  match a with
  | TRcd (l', t) when String.equal l l' -> Some t
  | TAnd (a1, a2) ->
    (match label_in l a1, label_in l a2 with
    | true, false -> srlookup_opt a1 l
    | false, true -> srlookup_opt a2 l
    | _ -> None)
  | _ -> None

let srlookup (a : typ) (l : string) : typ =
  match srlookup_opt a l with
  | Some t  -> t
  | None    -> elab_error ("no unambiguous field labelled " ^ l)

(* LinkOk: Γ₁ satisfies every labelled import of the interface
   D ::= rcd l A | D & rcd l A (left-nested intersections of records). *)
let rec link_ok (g1 : typ) (d : typ) : bool =
  let import_ok l a = match srlookup_opt g1 l with
                        | Some a' -> a' = a
                        | None    -> false
  in  match d with
      | TRcd (l, a) -> import_ok l a
      | TAnd (d', TRcd (l, a)) -> link_ok g1 d' && import_ok l a
      | _ -> false

(* type elaboration *)

let rec elab_typ : typ -> C.typ = function
  | TInt        -> C.TInt
  | TTop        -> C.TTop
  | TArr (a, b) -> C.TArr (elab_typ a, elab_typ b)
  | TAnd (a, b) -> C.TAnd (elab_typ a, elab_typ b)
  | TOr  (a, b) -> C.TOr  (elab_typ a, elab_typ b)
  | TRcd (l, a) -> C.TRcd (l, elab_typ a)
  | TSig mt     -> elab_modtyp mt
  | TVar n      -> C.TVar n
  | TMu t       -> C.TMu (elab_typ t)

and elab_modtyp : modtyp -> C.typ = function
  | TyIntf t        -> elab_typ t
  | TyArrM (t, mt)  -> C.TArr (elab_typ t, elab_modtyp mt)

let elab_lit : lit -> C.lit = function
  | Int n     -> C.Int n
  | Bool b    -> C.Bool b
  | String s  -> C.String s

let typ_of_lit : lit -> typ = function
  | Int _     -> TInt
  | Bool _    -> TTop
  | String _  -> TTop

(* elaboration utilities *)

(* non-dependent merge core λE level *)
let nmrg_core (ctx: C.typ) (ce1 : C.exp) (ce2 : C.exp) : C.exp =
  C.App
    (C.Lam
       (ctx,
        C.Mrg
          (C.Box (C.Proj (C.Query, 0), ce1),
           C.Box (C.Proj (C.Query, 1), ce2))),
     C.Query)

(* linked core: term produced at the core linking level *)
let linked_core (ctx : C.typ) (l : string) (ce1 : C.exp) (ce2 : C.exp) : C.exp =
  C.App
    (C.Lam
       (ctx,
        C.Mrg
          (C.Box (C.Proj (C.Query, 0), ce1),
           C.Box
             (C.Proj (C.Query, 1),
              C.App (ce2, C.Lrec (l, C.Rproj (ce1, l)))))),
     C.Query)

(* wireArg: build the import package for interface d by projecting each
   labelled import out of ce1 *)
let rec wire_arg (ctx : C.typ) (ce1 : C.exp) : typ -> C.exp = function
  | TRcd (l, _) -> C.Lrec (l, C.Rproj (ce1, l))
  | TAnd (d, TRcd (l, _)) ->
    nmrg_core ctx (wire_arg ctx ce1 d) (C.Lrec (l, C.Rproj (ce1, l)))
  | _ -> C.Unit

let linked_core_n (ctx : C.typ) (d : typ) (ce1 : C.exp) (ce2 : C.exp) : C.exp =
  C.App
    (C.Lam
       (ctx,
        C.Mrg
          (C.Box (C.Proj (C.Query, 0), ce1),
           C.Box (C.Proj (C.Query, 1), C.App (ce2, wire_arg ctx ce1 d)))),
     C.Query)

(* ---- elaboration based on the `elabExp` judgment ---- *)

let rec elab (ctx : typ) (e : exp) : typ * C.exp =
  match e with
  | Query -> (ctx, C.Query)
  | Lit l -> (typ_of_lit l, C.Lit (elab_lit l))
  | Unit -> (TTop, C.Unit)
  | Lam (a, body) ->
    let b, ce = elab (TAnd (ctx, a)) body in
    (TArr (a, b), C.Lam (elab_typ a, ce))
  | Clos (v, a, body) ->
    if not (is_value v) then elab_error "closure environment must be a value";
    let ctx', ce1 = elab TTop v in
    let b, ce2 = elab (TAnd (ctx', a)) body in
    (TArr (a, b), C.Clos (ce1, elab_typ a, ce2))
  | App (e1, e2) ->
    (match elab ctx e1 with
     | TArr (a, b), ce1 ->
       let a', ce2 = elab ctx e2 in
       if a' = a then (b, C.App (ce1, ce2))
       else elab_error "argument type mismatch"
     | _ -> elab_error "application of a non-function")
  | Box (e1, e2) ->
    let ctx', ce1 = elab ctx e1 in
    let a, ce2 = elab ctx' e2 in
    (a, C.Box (ce1, ce2))
  | Mrg (e1, e2) ->
    let a, ce1 = elab ctx e1 in
    let b, ce2 = elab (TAnd (ctx, a)) e2 in
    (TAnd (a, b), C.Mrg (ce1, ce2))
  | Nmrg (e1, e2) ->
    let a, ce1 = elab ctx e1 in
    let b, ce2 = elab ctx e2 in
    (TAnd (a, b), nmrg_core (elab_typ ctx) ce1 ce2)
  | Proj (e1, i) ->
    let a, ce = elab ctx e1 in
    (slookup a i, C.Proj (ce, i))
  | Lrec (l, e1) ->
    let a, ce = elab ctx e1 in
    (TRcd (l, a), C.Lrec (l, ce))
  | Rproj (e1, l) ->
    let b, ce = elab ctx e1 in
    (srlookup b l, C.Rproj (ce, l))
  | Letb (e1, ann, e2) ->
    let a, ce1 = elab ctx e1 in
    if a <> ann then
      elab_error "let annotation does not match the bound expression";
    let b, ce2 = elab (TAnd (ctx, a)) e2 in
    (b, C.App (C.Lam (elab_typ a, ce2), ce1))
  | Openm (e1, e2) ->
    (match elab ctx e1 with
     | TRcd (l, a), ce1 ->
       let b, ce2 = elab (TAnd (ctx, a)) e2 in
       (b, C.App (C.Lam (elab_typ a, ce2), C.Rproj (ce1, l)))
     | _ -> elab_error "open subject must be a labelled record")
  | Mstruct (Sandboxed, body) ->
    let b, ce = elab TTop body in
    (b, C.Box (C.Unit, ce))
  | Mstruct (Open, body) ->
    let b, ce = elab ctx body in
    (b, C.Box (C.Query, ce))
  | Mfunctor (Sandboxed, a, body) ->
    let b, ce = elab (TAnd (TTop, a)) body in
    (TSig (TyArrM (a, TyIntf b)), C.Box (C.Unit, C.Lam (elab_typ a, ce)))
  | Mfunctor (Open, a, body) ->
    let b, ce = elab (TAnd (ctx, a)) body in
    (TSig (TyArrM (a, TyIntf b)), C.Lam (elab_typ a, ce))
  | Mclos (v, a, body) ->
    if not (is_value v) then
      elab_error "module closure environment must be a value";
    let ctx', ce1 = elab TTop v in
    let b, ce2 = elab (TAnd (ctx', a)) body in
    (TSig (TyArrM (a, TyIntf b)), C.Clos (ce1, elab_typ a, ce2))
  | Mapp (e1, e2) ->
    (match elab ctx e1 with
     | TSig (TyArrM (a, TyIntf b)), ce1 ->
       let a', ce2 = elab ctx e2 in
       if a' = a then (b, C.App (ce1, ce2))
       else elab_error "functor argument type mismatch"
     | _ -> elab_error "module application of a non-functor")
  | Mlink (e1, e2) ->
    let g1, ce1 = elab ctx e1 in
    (match elab ctx e2 with
     | TSig (TyArrM (TRcd (l, a), TyIntf b)), ce2 ->
       (match srlookup_opt g1 l with
        | Some a' when a' = a ->
          (TAnd (g1, b), linked_core (elab_typ ctx) l ce1 ce2)
        | Some _ -> elab_error ("import " ^ l ^ " has a mismatched type")
        | None ->
          elab_error ("no unambiguous field labelled " ^ l ^ " to link against"))
     | _ -> elab_error "link target must be a functor with a single record import")
  | Mlinkn (e1, e2) ->
    let g1, ce1 = elab ctx e1 in
    (match elab ctx e2 with
     | TSig (TyArrM (d, TyIntf b)), ce2 ->
       if link_ok g1 d
       then (TAnd (g1, b), linked_core_n (elab_typ ctx) d ce1 ce2)
       else elab_error "module does not satisfy every labelled import"
     | _ -> elab_error "n-ary link target must be a functor")
  | Inl (b, e1) ->
    let a, ce = elab ctx e1 in
    (TOr (a, b), C.Inl (elab_typ b, ce))
  | Inr (a, e1) ->
    let b, ce = elab ctx e1 in
    (TOr (a, b), C.Inr (elab_typ a, ce))
  | Case (e1, el, er) ->
    (match elab ctx e1 with
     | TOr (a, b), ce ->
       let c1, ce1 = elab (TAnd (ctx, a)) el in
       let c2, ce2 = elab (TAnd (ctx, b)) er in
       if c1 = c2 then (c1, C.Case (ce, ce1, ce2))
       else elab_error "case branches have different types"
     | _ -> elab_error "case scrutinee is not a union")
  | Flam (a, b, body) ->
    let b', ce = elab (TAnd (TAnd (ctx, TArr (a, b)), a)) body in
    if b' = b then (TArr (a, b), C.Flam (elab_typ a, elab_typ b, ce))
    else elab_error "recursive function body type mismatch"
  | Fclos (v, a, b, body) ->
    if not (is_value v) then elab_error "closure environment must be a value";
    let ctx', ce1 = elab TTop v in
    let b', ce2 = elab (TAnd (TAnd (ctx', TArr (a, b)), a)) body in
    if b' = b then (TArr (a, b), C.Fclos (ce1, elab_typ a, elab_typ b, ce2))
    else elab_error "recursive function body type mismatch"
  | Fold (t, e1) ->
    let a, ce = elab ctx e1 in
    if a = unfold_mu t then (TMu t, C.Fold (elab_typ t, ce))
    else elab_error "fold body does not match unrolled type"
  | Unfold e1 ->
    (match elab ctx e1 with
     | TMu t, ce -> (unfold_mu t, C.Unfold ce)
     | _ -> elab_error "unfold applied to a non-recursive type")

(* ---- wrappers (whole programs elaborate under ⊤, per whole_program_correctness) ---- *)

let check (e : exp) : typ = fst (elab TTop e)

let compile (e : exp) : C.exp = snd (elab TTop e)