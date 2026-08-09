(* Desugaring layer from Source to SCE (source core).

   Names are already gone — Debruijn turned them into paths — so this pass is a
   translation that synthesizes types along the way. It has to synthesize
   because the core demands types this pass cannot omit:

     - `Letb` carries a mandatory annotation;
     - application is `App` for a function and `Mapp` for a functor;
     - `Inl`/`Inr`/`Fold` carry a type no local rule can infer, which is what
       the surface ascription `(e : A)` is for.

   The typing rules mirror lib/sce/elab.ml, and its judgement helpers are
   reused rather than reimplemented. *)

open Ast
module S = Sce_core.Ast
module E = Sce_core.Elab
module P = Sce_core.Pretty

exception Error of string * loc

let err loc fmt = Printf.ksprintf (fun s -> raise (Error (s, loc))) fmt

(* The judgement helpers in Elab signal failure with their own exception. *)
let lift loc f = try f () with E.Elab_error m -> raise (Error (m, loc))

let mismatch loc what expected got =
  err loc "%s: expected %s, got %s" what (P.typ_to_string expected)
    (P.typ_to_string got)

module F = Frames.Make (struct
  type t = S.typ
end)

(* `base` is the context a `box` or a sandbox installed underneath the slots;
   it is Top everywhere else. Keeping it explicit makes `ctx` exact rather than
   merely a left-nested approximation. *)
type env = { slots : F.env; base : S.typ }

let empty_env = { slots = F.empty; base = S.TTop }

let ctx env = List.fold_left (fun acc t -> S.TAnd (acc, t)) env.base (List.rev env.slots)

let slot env loc i =
  match F.nth env.slots i with
  | Some t -> t
  | None -> err loc "no context component at index %d" i

let reset env = { slots = F.sandbox env.slots; base = S.TTop }

(* ---------------- types ---------------- *)

let rec conv_typ (t : int typ) : S.typ =
  match t.it with
  | TInt -> S.TInt
  | TBool -> S.TBool
  | TString -> S.TString
  | TTop -> S.TTop
  | TVar i -> S.TVar i
  | TArr (a, b) -> S.TArr (conv_typ a, conv_typ b)
  | TAnd (a, b) -> S.TAnd (conv_typ a, conv_typ b)
  | TOr (a, b) -> S.TOr (conv_typ a, conv_typ b)
  | TMu (_, b) -> S.TMu (conv_typ b)
  (* `A => B => C` is a curried functor, which is exactly the shape
     `Mfunctor` produces: the result is an interface that is itself a
     signature, never a nested `TyArrM`. *)
  | TSig (a, b) -> S.TSig (S.TyArrM (conv_typ a, S.TyIntf (conv_typ b)))
  | TRcd fs -> (
    match fs with
    | [] -> S.TTop
    | (l, ft) :: rest ->
      List.fold_left
        (fun acc (l, ft) -> S.TAnd (acc, S.TRcd (l, conv_typ ft)))
        (S.TRcd (l, conv_typ ft))
        rest)

let conv_lit = function
  | LInt n -> (S.TInt, S.Int n)
  | LBool b -> (S.TBool, S.Bool b)
  | LString s -> (S.TString, S.String s)

let conv_binop = function
  | Add -> S.Add | Sub -> S.Sub | Mul -> S.Mul | Div -> S.Div | Mod -> S.Mod
  | Lt -> S.Lt | Le -> S.Le | Gt -> S.Gt | Ge -> S.Ge
  | Eq -> S.Eq | Ne -> S.Ne | Cat -> S.Cat
  | And | Or -> assert false (* eliminated into If below *)

let btrue = S.Lit (S.Bool true)
let bfalse = S.Lit (S.Bool false)

(* ---------------- expressions ---------------- *)

let rec desugar env (e : (path, int) exp) : S.typ * S.exp =
  match e.it with
  | EVar (PIdx i) -> (slot env e.loc i, S.Proj (S.Query, i))
  | EVar (PField (i, l)) ->
    let t = slot env e.loc i in
    (lift e.loc (fun () -> E.srlookup t l), S.Rproj (S.Proj (S.Query, i), l))
  | ELit l ->
    let t, cl = conv_lit l in
    (t, S.Lit cl)
  | EUnit -> (S.TTop, S.Unit)
  | EQuery -> (ctx env, S.Query)
  | EIndex (e1, n) ->
    let t, c = desugar env e1 in
    (lift e.loc (fun () -> E.slookup t n), S.Proj (c, n))
  | EAnnot (inner, t) -> ascribe env e.loc inner (conv_typ t)
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
  (* `&&`, `||` and `not` are short-circuiting sugar for `if`; unary minus is
     sugar for subtraction. None of them reach the core. *)
  | EBinop (And, a, b) ->
    let ca = expect_bool env a in
    let cb = expect_bool env b in
    (S.TBool, S.If (ca, cb, bfalse))
  | EBinop (Or, a, b) ->
    let ca = expect_bool env a in
    let cb = expect_bool env b in
    (S.TBool, S.If (ca, btrue, cb))
  | EBinop (op, a, b) ->
    let ta, ca = desugar env a in
    let tb, cb = desugar env b in
    ( lift e.loc (fun () -> E.typ_of_binop (conv_binop op) ta tb),
      S.Binop (conv_binop op, ca, cb) )
  | EUnop (Not, a) -> (S.TBool, S.If (expect_bool env a, bfalse, btrue))
  | EUnop (Neg, a) ->
    let ta, ca = desugar env a in
    if ta <> S.TInt then mismatch a.loc "negation" S.TInt ta;
    (S.TInt, S.Binop (S.Sub, S.Lit (S.Int 0), ca))
  | EIf (c, t, f) ->
    let cc = expect_bool env c in
    let tt, ct = desugar env t in
    let tf, cf = desugar env f in
    if tt <> tf then mismatch f.loc "the branches of `if` disagree" tt tf;
    (tt, S.If (cc, ct, cf))
  | ELam (ps, body) -> lambdas env ps body
  | EApp (f, a) -> (
    let tf, cf = desugar env f in
    match tf with
    | S.TArr (dom, cod) ->
      let ta, ca = desugar env a in
      if ta <> dom then mismatch a.loc "argument" dom ta;
      (cod, S.App (cf, ca))
    | S.TSig (S.TyArrM (dom, S.TyIntf cod)) ->
      let ta, ca = desugar env a in
      if ta <> dom then mismatch a.loc "functor argument" dom ta;
      (cod, S.Mapp (cf, ca))
    | _ ->
      err f.loc "this is applied to an argument but has type %s"
        (P.typ_to_string tf))
  | ERcd [] -> (S.TTop, S.Unit)
  | ERcd ((l, fe) :: rest) ->
    (* Fields are independent, so the record is a non-dependent merge chain. *)
    let t0, c0 = desugar env fe in
    List.fold_left
      (fun (accT, accC) (l, fe) ->
        let t, c = desugar env fe in
        (S.TAnd (accT, S.TRcd (l, t)), S.Nmrg (accC, S.Lrec (l, c))))
      (S.TRcd (l, t0), S.Lrec (l, c0))
      rest
  | EField (b, l) ->
    let t, c = desugar env b in
    (lift e.loc (fun () -> E.srlookup t l), S.Rproj (c, l))
  | EMerge (MNon, a, b) ->
    let ta, ca = desugar env a in
    let tb, cb = desugar { env with slots = F.nmrg ta env.slots } b in
    (S.TAnd (ta, tb), S.Nmrg (ca, cb))
  | EMerge (MDep, a, b) ->
    let ta, ca = desugar env a in
    let tb, cb = desugar { env with slots = F.mrg ta env.slots } b in
    (S.TAnd (ta, tb), S.Mrg (ca, cb))
  | ELet (b, body) ->
    let vt, cv = binding env b in
    let bt, cb = desugar { env with slots = F.letb vt env.slots } body in
    (bt, S.Letb (cv, vt, cb))
  | EOpen (m, body) ->
    let mt, cm = desugar env m in
    let bt, cb = desugar { env with slots = F.openm mt env.slots } body in
    (bt, S.Openm (S.Lrec (open_label, cm), cb))
  | EBox (m, body) ->
    let mt, cm = desugar env m in
    let bt, cb = desugar { slots = F.box env.slots; base = mt } body in
    (bt, S.Box (cm, cb))
  | ECase (scrut, _, e1, _, e2) -> (
    let ts, cs = desugar env scrut in
    match ts with
    | S.TOr (a, b) ->
      let t1, c1 = desugar { env with slots = F.case_branch a env.slots } e1 in
      let t2, c2 = desugar { env with slots = F.case_branch b env.slots } e2 in
      if t1 <> t2 then mismatch e2.loc "the branches of `case` disagree" t1 t2;
      (t1, S.Case (cs, c1, c2))
    | _ ->
      err scrut.loc "`case` expects a union type, got %s" (P.typ_to_string ts))
  | EStruct (sb, ds) ->
    let env0 = match sb with Sandboxed -> reset env | Open -> env in
    let t, c = structure env0 ds in
    (t, S.Mstruct (conv_sandbox sb, c))
  | EFunctor (sb, ps, body) -> functors env sb ps body
  | ELink (k, m, f) -> link env e.loc k m f

and open_label = "%open"

and conv_sandbox = function Sandboxed -> S.Sandboxed | Open -> S.Open

and expect_bool env e =
  let t, c = desugar env e in
  if t <> S.TBool then mismatch e.loc "condition" S.TBool t;
  c

(* Ascription has no core counterpart; it is a check here, and it is what
   supplies the types `Inl`, `Inr` and `Fold` cannot infer. *)
and ascribe env loc (inner : (path, int) exp) (ty : S.typ) =
  match (inner.it, ty) with
  | EInl a, S.TOr (l, r) ->
    let ta, ca = desugar env a in
    if ta <> l then mismatch a.loc "left injection" l ta;
    (ty, S.Inl (r, ca))
  | EInr a, S.TOr (l, r) ->
    let ta, ca = desugar env a in
    if ta <> r then mismatch a.loc "right injection" r ta;
    (ty, S.Inr (l, ca))
  | (EInl _ | EInr _), _ ->
    err loc "an injection must be ascribed a union type, got %s"
      (P.typ_to_string ty)
  | EFold a, S.TMu body ->
    let ta, ca = desugar env a in
    let unrolled = E.unfold_mu body in
    if ta <> unrolled then mismatch a.loc "fold body" unrolled ta;
    (ty, S.Fold (body, ca))
  | EFold _, _ ->
    err loc "`fold` must be ascribed a recursive type, got %s"
      (P.typ_to_string ty)
  | _ ->
    let t, c = desugar env inner in
    if t <> ty then mismatch loc "type annotation" ty t;
    (ty, c)

and lambdas env ps body =
  match ps with
  | [] -> desugar env body
  | p :: rest ->
    let a = conv_typ p.p_typ in
    let bt, cb = lambdas { env with slots = F.lam a env.slots } rest body in
    (S.TArr (a, bt), S.Lam (a, cb))

(* Only the outermost functor carries the sandbox flag; the curried ones inside
   it inherit an already-sandboxed context. *)
and functors env sb ps body =
  match ps with
  | [] -> desugar env body
  | p :: rest ->
    let a = conv_typ p.p_typ in
    let inner =
      match sb with
      | Sandboxed -> { slots = F.lam a (reset env).slots; base = S.TTop }
      | Open -> { env with slots = F.lam a env.slots }
    in
    let bt, cb = functors inner Open rest body in
    ( S.TSig (S.TyArrM (a, S.TyIntf bt)),
      S.Mfunctor (conv_sandbox sb, a, cb) )

and link env loc k m f =
  let mt, cm = desugar env m in
  let ft, cf = desugar env f in
  match ft with
  | S.TSig (S.TyArrM (imports, S.TyIntf result)) ->
    (* Pre-check the import wiring so the error names the offending label
       instead of surfacing from the elaborator later. *)
    (match k with
     | LOne -> (
       match imports with
       | S.TRcd (l, a) -> (
         match E.srlookup_opt mt l with
         | Some a' when a' = a -> ()
         | Some a' ->
           err loc "import '%s' has type %s but the module provides %s" l
             (P.typ_to_string a) (P.typ_to_string a')
         | None -> err loc "the module has no unambiguous field '%s' to link against" l)
       | _ ->
         err loc
           "`link` needs a functor importing exactly one record; use `linkall` \
            for several")
     | LAll ->
       if not (E.link_ok mt imports) then
         err loc "the module does not satisfy every labelled import of %s"
           (P.typ_to_string imports));
    ( S.TAnd (mt, result),
      match k with LOne -> S.Mlink (cm, cf) | LAll -> S.Mlinkn (cm, cf) )
  | _ ->
    err loc "the target of `link` must be a functor, but has type %s"
      (P.typ_to_string ft)

and binding env (b : (path, int) binding) : S.typ * S.exp =
  if b.b_rec then recursive_binding env b
  else
    let rec go env ps =
      match ps with
      | [] ->
        let bt, cb = desugar env b.b_exp in
        (match b.b_ann with
         | Some t ->
           let want = conv_typ t in
           if bt <> want then mismatch b.b_exp.loc "annotation" want bt
         | None -> ());
        (bt, cb)
      | p :: rest ->
        let a = conv_typ p.p_typ in
        let bt, cb = go { env with slots = F.lam a env.slots } rest in
        (S.TArr (a, bt), S.Lam (a, cb))
    in
    go env b.b_params

(* `Flam (A, B, body)` types its body under `(ctx & (A -> B)) & A`, so the
   recursive name sits *below* the parameters. Extra parameters become plain
   lambdas inside it. *)
and recursive_binding env (b : (path, int) binding) : S.typ * S.exp =
  let ret =
    match b.b_ann with
    | Some t -> conv_typ t
    | None ->
      err b.b_bind.bd_loc
        "'let rec %s' needs a return type annotation: the recursive call has \
         to be typed before the body is checked" b.b_bind.bd_name
  in
  match b.b_params with
  | [] ->
    err b.b_bind.bd_loc "'let rec %s' needs at least one parameter"
      b.b_bind.bd_name
  | p :: rest ->
    let a = conv_typ p.p_typ in
    let rest_tys = List.map (fun p -> conv_typ p.p_typ) rest in
    let cod = List.fold_right (fun d acc -> S.TArr (d, acc)) rest_tys ret in
    let self = S.TArr (a, cod) in
    let inner = { env with slots = F.flam ~self ~arg:a env.slots } in
    let rec go env tys =
      match tys with
      | [] ->
        let bt, cb = desugar env b.b_exp in
        if bt <> ret then mismatch b.b_exp.loc "recursive function body" ret bt;
        cb
      | d :: more -> S.Lam (d, go { env with slots = F.lam d env.slots } more)
    in
    (self, S.Flam (a, cod, go inner rest_tys))

(* A structure is a left-nested *dependent* merge chain, so each declaration
   sees one extra slot holding everything declared before it. *)
and structure env (ds : (path, int) decl list) : S.typ * S.exp =
  let rec go env chain ds =
    let here =
      match chain with
      | None -> env
      | Some (t, _) -> { env with slots = F.mrg t env.slots }
    in
    let add (t, c) =
      match chain with
      | None -> (t, c)
      | Some (pt, pc) -> (S.TAnd (pt, t), S.Mrg (pc, c))
    in
    match ds with
    | [] -> (
      match chain with Some tc -> tc | None -> (S.TTop, S.Unit))
    | d :: rest -> (
      match d.it with
      (* Aliases were expanded at their use sites by Debruijn. *)
      | DType _ -> go env chain rest
      | DLet b ->
        let vt, cv = binding here b in
        let l = b.b_bind.bd_name in
        go env (Some (add (S.TRcd (l, vt), S.Lrec (l, cv)))) rest
      | DModule (bn, me) ->
        let vt, cv = desugar here me in
        let l = bn.bd_name in
        go env (Some (add (S.TRcd (l, vt), S.Lrec (l, cv)))) rest
      | DOpen m ->
        (* The declarations after an `open` become its body and start a fresh
           chain on top of the opened slot. *)
        let mt, cm = desugar here m in
        let inner = { here with slots = F.openm mt here.slots } in
        let rt, rc = go inner None rest in
        add (rt, S.Openm (S.Lrec (open_label, cm), rc)))
  in
  go env None ds

(* ---------------- programs ----------------

   Top-level declarations chain with `Letb`, so each binds a plain slot. *)

let desugar_program (p : Ast.indexed) : S.typ * S.exp =
  let main =
    match p.main with
    | Some e -> e
    | None -> { it = EUnit; loc = dummy_loc }
  in
  let rec go env ds =
    match ds with
    | [] -> desugar env main
    | d :: rest -> (
      match d.it with
      | DType _ -> go env rest
      | DLet b ->
        let vt, cv = binding env b in
        let bt, cb = go { env with slots = F.letb vt env.slots } rest in
        (bt, S.Letb (cv, vt, cb))
      | DModule (_, me) ->
        let vt, cv = desugar env me in
        let bt, cb = go { env with slots = F.letb vt env.slots } rest in
        (bt, S.Letb (cv, vt, cb))
      | DOpen m ->
        let mt, cm = desugar env m in
        let bt, cb = go { env with slots = F.openm mt env.slots } rest in
        (bt, S.Openm (S.Lrec (open_label, cm), cb)))
  in
  go empty_env p.decls
