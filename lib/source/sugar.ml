(* Desugaring layer from Source to SCE (source core). *)

open Ast
module S = Sce_core.Ast
module E = Sce_core.Elab
module P = Sce_core.Pretty

exception Error of string * loc

let err loc fmt = Printf.ksprintf (fun s -> raise (Error (s, loc))) fmt

(* 
  The judgement helpers in Elab signal failures with their own exception 
  Basically, takes the elaboration error, and raises it to the desugaring error
  with `loc`.

  Run `f`, get `elab error` and then, raise it.
*)
let lift loc f = 
  try f () with 
    E.Elab_error m -> raise (Error (m, loc))

let ty_mismatch loc what expected got =
  err loc "%s: expected %s, got %s" what (P.typ_to_string expected)
    (P.typ_to_string got)

module F = Frames.Make (struct type t = S.typ end)

(*
  `base` is the context a `box` or a sandbox installed underneath
  the slots; it is Top everywhere else.
*)
type env      = { slots : F.env; base : S.typ }

let empty_env = { slots = F.empty; base = S.TTop }

let ctx env =
  List.fold_left 
    (fun acc t -> S.TAnd (acc, t)) 
    env.base 
    (List.rev env.slots)

let slot env loc i =
  match F.nth env.slots i with
  | Some t  -> t
  | None    -> err loc "no context component at index %d" i

let reset env = { slots = F.sandbox env.slots; base = S.TTop }

(* Types desugaring *)
let rec conv_typ (t : int typ) : S.typ =
  match t.it with
  | TInt    -> S.TInt
  | TBool   -> S.TBool
  | TString -> S.TString
  | TTop    -> S.TTop
  | TVar i  -> S.TVar i
  | TArr (a, b) -> S.TArr (conv_typ a, conv_typ b)
  | TAnd (a, b) -> S.TAnd (conv_typ a, conv_typ b)
  | TOr  (a, b) -> S.TOr  (conv_typ a, conv_typ b)
  | TMu  (_x, a) -> S.TMu (conv_typ a)
  | TSig (a, b) -> S.TSig (S.TyArrM (conv_typ a, S.TyIntf (conv_typ b)))
  | TRcd ls -> (
    match ls with
    | [] -> S.TTop
    | (l, ft) :: rest ->
      List.fold_left
        (fun acc (l, ft) -> 
          S.TAnd (acc, S.TRcd (l, conv_typ ft)))
        (S.TRcd (l, conv_typ ft))
        rest
    )

let conv_lit = function
  | LInt n    -> (S.TInt,    S.Int n)
  | LBool b   -> (S.TBool,   S.Bool b)
  | LString s -> (S.TString, S.String s)

let conv_binop = function
  | Add -> S.Add | Sub -> S.Sub | Mul -> S.Mul | Div -> S.Div | Mod -> S.Mod
  | Lt -> S.Lt | Le -> S.Le | Gt -> S.Gt | Ge -> S.Ge
  | Eq -> S.Eq | Ne -> S.Ne | Cat -> S.Cat
  (* eliminated *)
  | And | Or -> assert false

let btrue = S.Lit (S.Bool true)
let bfalse = S.Lit (S.Bool false)

(*
  An `%open` is a label used to wrap a pure record
  when `open m in ...` is directly used with `m` not a record.
  So, it wraps in {`%open` : m} and then, de-sugars further,
  allowing later to unwrap. 
*)
let open_label = "%open"

(* desugaring is type-directed
 as info is required
*)
let rec desugar env (e : (path, int) exp) : S.typ * S.exp =
  match e.it with
  (* x ~> ?.i *)
  | EVar (PIdx i) -> (slot env e.loc i, S.Proj (S.Query, i))
  (* x ~> ?.i.l *)
  | EVar (PField (i, l)) ->
    let t = slot env e.loc i in
    (lift e.loc (fun () -> E.srlookup t l), S.Rproj (S.Proj (S.Query, i), l))
  | ELit l ->
    let t, cl = conv_lit l in
    (t, S.Lit cl)
  (* Just avoiding noise for now *)
  | EUnit           -> (S.TTop, S.Unit)
  | EQuery          -> (ctx env, S.Query)
  | EIndex (e1, n)  ->
    let t, c = desugar env e1 in
    (lift e.loc (fun () -> E.slookup t n), S.Proj (c, n))
  | EAnnot (e, ty)  ->
    ascribe env e.loc e (conv_typ ty)
  | EInl _ | EInr _ ->
    err e.loc
      "an injection needs a type ascription so the other side of the union is \
       known, as in `(inl e : A | B)`"
  | EFold _ ->
    err e.loc
      "`fold` needs a type ascription naming the recursive type, as in \
       `(fold e : mu a. A)`"
  | EUnfold e1 -> (
    let t, c = desugar env e1 in
    match t with
    | S.TMu body -> (E.unfold_mu body, S.Unfold c)
    | _ -> 
      err e1.loc "`unfold` expects a recursive type, got %s" (P.typ_to_string t))
  (* `&&` and `||` are short-circuiting sugar for `if`; they never reach the
     core, which is why `conv_binop` asserts on them. *)
  | EBinop (And, e1, e2) ->
  (* 
    expect_bool ensures e1 desugared has Bool type,
    otherwise it throws an error.
  *)
    let c1 = expect_bool env e1 in
    let c2 = expect_bool env e2 in
    (S.TBool, S.If (c1, c2, bfalse))
  | EBinop (Or, e1, e2) ->
    let c1 = expect_bool env e1 in
    let c2 = expect_bool env e2 in
    (S.TBool, S.If (c1, btrue, c2))
  | EBinop (bop, e1, e2) ->
    let ty1, c1 = desugar env e1 in
    let ty2, c2 = desugar env e2 in
    ( lift e.loc (fun () -> E.typ_of_binop (conv_binop bop) ty1 ty2),
      S.Binop (conv_binop bop, c1, c2) )
  (* `not` and unary `-` are sugar too: the core has no unary operators. *)
  | EUnop (Not, e1) -> (S.TBool, S.If (expect_bool env e1, bfalse, btrue))
  | EUnop (Neg, e1) ->
    let t, c = desugar env e1 in
    if t <> S.TInt then ty_mismatch e1.loc "negation" S.TInt t;
    (S.TInt, S.Binop (S.Sub, S.Lit (S.Int 0), c))
  (* No subtyping, so there is no join to compute: the branches must agree. *)
  | EIf (c, t, f) ->
    let cc      = expect_bool env c in
    let tt, ct  = desugar env t     in
    let tf, cf  = desugar env f     in
    if tt <> tf 
      then ty_mismatch f.loc "the branches of `if` disagree" tt tf;
    (tt, S.If (cc, ct, cf))
  (* Curried: the parameters extend the context left to right, but the term
     nests right to left — hence fold_left for the env, fold_right to build. *)
  | ELam (params, body) ->
    let tys = List.map (fun p -> conv_typ p.p_typ) params in
    (* This is constructing the environment by pushing the 
      lambda arguments into the environment *)
    let env' = 
      List.fold_left
        (fun env a -> 
          { slots = F.lam a env.slots; base = env.base })
        env tys                    in
    let bt, cb = desugar env' body in
    List.fold_right (fun a (t, c) -> (S.TArr (a, t), S.Lam (a, c))) tys (bt, cb)
  (* Here, we overload application,
    and then, use types to decide whether it is a functor
    or function application. *)
  | EApp (e1, e2) ->
    let ty1, c1 = desugar env e1 in
    let ty2, c2 = desugar env e2 in
    (match ty1 with
     | S.TArr (dom, cod) ->
       if ty2 <> dom then ty_mismatch e2.loc "argument" dom ty2;
       (cod, S.App (c1, c2))
     | S.TSig (S.TyArrM (dom, S.TyIntf cod)) ->
       if ty2 <> dom then ty_mismatch e2.loc "functor argument" dom ty2;
       (cod, S.Mapp (c1, c2))
     | _ ->
       err e1.loc "this is applied to an argument but has type %s"
         (P.typ_to_string ty1))
  | ERcd []   -> (S.TTop, S.Unit)
  (* Nmrg, and every field desugared under the *same* env — matching Debruijn,
     which pushes no slot for a record literal. *)
  | ERcd ((l, fe) :: rest) ->
    let t0, c0 = desugar env fe in
    List.fold_left
      (fun (accT, accC) (l, fe) ->
        let t, c = desugar env fe in
        (S.TAnd (accT, S.TRcd (l, t)), S.Nmrg (accC, S.Lrec (l, c))))
      (S.TRcd (l, t0), S.Lrec (l, c0))
      rest
  | EField _  -> err e.loc "TODO: EField"
  | EMerge _  -> err e.loc "TODO: EMerge"
  | ELet _    -> err e.loc "TODO: ELet"
  | EOpen _   -> err e.loc "TODO: EOpen"
  | ECase _   -> err e.loc "TODO: ECase"
  | EStruct _ -> err e.loc "TODO: EStruct"
  | EFunctor _ -> err e.loc "TODO: EFunctor"
  | ELink _   -> err e.loc "TODO: ELink"
  | EBox _    -> err e.loc "TODO: EBox"
  | EMatch _  -> err e.loc "TODO: EMatch"

and ascribe env loc (inner : (path, int) exp) (ty : S.typ) =
  match (inner.it, ty) with
  | EInl e, S.TOr (l, r) ->
    (* desugaring `e` gives its type *)
    (* `ta` is type of desugared SCE expression `ca` *)
    let ta, ce = desugar env e in
    if ta <> l
      then ty_mismatch e.loc "left injection" l ta;
    (ty, S.Inl (r, ce))
  | EInr e, S.TOr (l, r) ->
    let tb, ce = desugar env e in
    if tb <> r then ty_mismatch e.loc "right rejection" r tb;
    (ty, S.Inr (l, ce))
  | (EInl _ | EInr _), _ ->
    err loc "an injection must be ascribed a union type, got %s"
      (P.typ_to_string ty)
  | EFold e, S.TMu ty_body ->
    let ta, ce    = desugar env e    in
    let unrolled  = E.unfold_mu ty_body in
    if ta <> unrolled then ty_mismatch e .loc "fold body" unrolled ta;
    (ty, S.Fold (ty_body, ce))
  | EFold _, _ ->
    err loc "`fold` must be ascribed a recursive type, got %s"
      (P.typ_to_string ty)
  | _ ->
    let t, c = desugar env inner in
    if t <> ty then ty_mismatch loc "type annotation" ty t;
    (ty, c)

and expect_bool env e =
  let t, e' = desugar env e in
  if t <> S.TBool then
    ty_mismatch e.loc "condition" S.TBool t;
  e'
