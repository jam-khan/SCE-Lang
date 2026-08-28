(* Desugaring: named surface AST -> named λSCE.

   One pass does both halves of the front end's job, because they are the same
   job. It synthesizes the types the core demands and the surface omits:

     - `Letb` carries a mandatory annotation;
     - application is `App` for a function and `Mapp` for a functor;
     - `Inl`/`Inr`/`Fold` carry a type no local rule can infer, which is what
       the surface ascription `(e : A)` is for.

   And it resolves names — a surface name is either a slot of the context or an
   unambiguous *field* of one (a struct's earlier declarations, an `open`, the
   left half of a dependent merge). Deciding which needs the labels each slot
   carries, which is exactly what those synthesized types record, so `Elab`'s
   own `srlookup_opt` answers it and no separate notion of "shape" is needed.

   What comes out is λSCE with names still on it. lib/sce/debruijn.ml turns each
   name into the index of the slot it denotes; the context discipline the two
   agree on lives in lib/sce/frames.ml.

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

(* ---------------- the context ---------------- *)

(* A context slot. `Named` is a binder, reached by the name it introduced;
   `Fields` is anonymous — a merge chain, an `open`, a struct's declarations so
   far — and is reached by the labels of its type instead. Both occupy an
   index, so a slot we cannot name still has to be pushed. *)
type slot =
  | Named of string * S.typ
  | Fields of string * S.typ

let slot_typ = function Named (_, t) | Fields (_, t) -> t

module F = Sce_core.Frames.Make (struct
  type t = slot
end)

type env = {
  slots : F.env;
  base : S.typ;                    (* what a box or sandbox installed under the slots *)
  mus : string list;               (* mu binders in scope, innermost first *)
  aliases : (string * S.typ) list; (* alias bodies, already resolved and closed *)
}

let empty_env = { slots = F.empty; base = S.TTop; mus = []; aliases = [] }

(* `base` is the context a `box` or a sandbox installed underneath the slots;
   it is Top everywhere else. Keeping it explicit makes `ctx` exact rather than
   merely a left-nested approximation. *)
let ctx env =
  List.fold_left
    (fun acc s -> S.TAnd (acc, slot_typ s))
    env.base (List.rev env.slots)

let reset env = { env with slots = F.sandbox env.slots; base = S.TTop }

(* `push` is the Frames rule for the form being desugared, so the slot lands
   where Debruijn will count it. *)
let bind push x t env = { env with slots = push (Named (x, t)) env.slots }

(* An anonymous slot still needs a name of its own, since Debruijn resolves
   `Rproj (Var x, l)` by finding x. There is exactly one slot per depth, so the
   depth names it uniquely wherever it is in scope — and `%` cannot start a
   surface identifier, so it cannot collide with a binder. *)
let bind_fields push t env =
  let x = "%" ^ string_of_int (List.length env.slots) in
  (x, { env with slots = push (Fields (x, t)) env.slots })

(* A surface name is the innermost slot that provides it: a binder by its own
   name, an anonymous slot by an unambiguous label. Ambiguity is not a match —
   `Elab.srlookup` would refuse the projection anyway. *)
let find env x =
  let rec go = function
    | [] -> None
    | Named (y, t) :: rest ->
      if String.equal y x then Some (S.Var y, t) else go rest
    | Fields (y, t) :: rest -> (
      match E.srlookup_opt t x with
      | Some ft -> Some (S.Rproj (S.Var y, x), ft)
      | None -> go rest)
  in
  go env.slots

(* The labels an `open` brings into scope. *)
let rec labels_of = function
  | S.TRcd (l, _) -> [ l ]
  | S.TAnd (a, b) -> labels_of a @ labels_of b
  | _ -> []

(* Duplicate labels are not merely redundant: `Elab.srlookup_opt` refuses a
   label that occurs on both sides of an intersection, so a duplicate would
   make *both* copies unreachable. *)
let duplicate loc what l =
  err loc "duplicate field '%s' in this %s; it would be unreachable" l what

let check_no_duplicates loc what labels =
  let rec go seen = function
    | [] -> ()
    | l :: rest -> if List.mem l seen then duplicate loc what l else go (l :: seen) rest
  in
  go [] labels

(* Reported at the offending declaration rather than at the head of the list. *)
let check_no_duplicate_decls what ds =
  let rec go seen = function
    | [] -> ()
    | d :: rest -> (
      match name_of_decl d with
      | Some l when List.mem l seen -> duplicate d.loc what l
      | Some l -> go (l :: seen) rest
      | None -> go seen rest)
  in
  go [] ds

(* ---------------- types ---------------- *)

let rec conv_typ env (t : typ) : S.typ =
  match t.it with
  | TInt -> S.TInt
  | TBool -> S.TBool
  | TString -> S.TString
  | TTop -> S.TTop
  | TVar a -> (
    let rec index i = function
      | [] -> None
      | b :: rest -> if String.equal b a then Some i else index (i + 1) rest
    in
    match index 0 env.mus with
    | Some i -> S.TVar i
    | None -> (
      (* Alias bodies are resolved with an empty mu stack, so they are closed
         and can be dropped in under any number of mu binders unshifted. *)
      match List.assoc_opt a env.aliases with
      | Some rt -> rt
      | None -> err t.loc "unbound type name '%s'" a))
  | TArr (a, b) -> S.TArr (conv_typ env a, conv_typ env b)
  | TAnd (a, b) -> S.TAnd (conv_typ env a, conv_typ env b)
  | TOr (a, b) -> S.TOr (conv_typ env a, conv_typ env b)
  | TMu (b, body) -> S.TMu (conv_typ { env with mus = b.bd_name :: env.mus } body)
  (* `A => B => C` is a curried functor, which is exactly the shape `Mfunctor`
     produces: the result is an interface that is itself a signature, never a
     nested `TyArrM`. *)
  | TSig (a, b) -> S.TSig (S.TyArrM (conv_typ env a, S.TyIntf (conv_typ env b)))
  | TRcd fs -> (
    check_no_duplicates t.loc "record type" (List.map fst fs);
    match fs with
    | [] -> S.TTop
    | (l, ft) :: rest ->
      List.fold_left
        (fun acc (l, ft) -> S.TAnd (acc, S.TRcd (l, conv_typ env ft)))
        (S.TRcd (l, conv_typ env ft))
        rest)

(* A type written on its own, with nothing in scope: a `.scei` interface, once
   its own aliases have been expanded. *)
let conv_typ_closed (t : typ) : S.typ = conv_typ empty_env t

(* ---------------- named-level alias expansion ----------------

   A .scei interface is aliases + a type, resolved *before* it meets the
   importing file's scope — so its aliases are expanded syntactically here,
   producing a self-contained named type. A mu binder of the same name
   shadows an alias inside its body. *)

let rec subst_tname (name : string) (body : typ) (t : typ) : typ =
  let nd it = { it; loc = t.loc } in
  let s = subst_tname name body in
  match t.it with
  | TVar a -> if String.equal a name then body else t
  | TInt | TBool | TString | TTop -> t
  | TArr (a, b) -> nd (TArr (s a, s b))
  | TAnd (a, b) -> nd (TAnd (s a, s b))
  | TOr (a, b) -> nd (TOr (s a, s b))
  | TSig (a, b) -> nd (TSig (s a, s b))
  | TRcd fs -> nd (TRcd (List.map (fun (l, ft) -> (l, s ft)) fs))
  | TMu (b, t') -> if String.equal b.bd_name name then t else nd (TMu (b, s t'))

let expand_aliases (aliases : (binder * typ) list) (t : typ) : typ =
  (* each body is expanded against the earlier ones, so every substitution
     below introduces no further alias references *)
  let expanded =
    List.fold_left
      (fun acc (b, tb) ->
        let tb = List.fold_left (fun tt (n, bo) -> subst_tname n bo tt) tb acc in
        acc @ [ (b.bd_name, tb) ])
      [] aliases
  in
  List.fold_left (fun tt (n, bo) -> subst_tname n bo tt) t expanded

(* ---------------- leaves ---------------- *)

let conv_lit = function
  | LInt n -> (S.TInt, S.Int n)
  | LBool b -> (S.TBool, S.Bool b)
  | LString s -> (S.TString, S.String s)

let conv_binop = function
  | Add -> S.Add | Sub -> S.Sub | Mul -> S.Mul | Div -> S.Div | Mod -> S.Mod
  | Lt -> S.Lt | Le -> S.Le | Gt -> S.Gt | Ge -> S.Ge
  | Eq -> S.Eq | Ne -> S.Ne | Cat -> S.Cat
  | And | Or -> assert false (* eliminated into If below *)

let conv_sandbox = function Sandboxed -> S.Sandboxed | Open -> S.Open

let btrue = S.Lit (S.Bool true)
let bfalse = S.Lit (S.Bool false)

(* The label an `open` subject is wrapped in, so `Openm` sees a record. *)
let open_label = "%open"

(* ---------------- expressions ---------------- *)

let rec desugar env (e : exp) : S.typ * S.named =
  match e.it with
  | EVar x -> (
    match find env x with
    | Some (occ, t) -> (t, occ)
    | None -> err e.loc "unbound variable '%s'" x)
  | ELit l ->
    let t, cl = conv_lit l in
    (t, S.Lit cl)
  | EUnit -> (S.TTop, S.Unit)
  | EQuery -> (ctx env, S.Query)
  | EIndex (e1, n) ->
    let t, c = desugar env e1 in
    (lift e.loc (fun () -> E.slookup t n), S.Proj (c, n))
  | EAnnot (inner, t) -> ascribe env e.loc inner (conv_typ env t)
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
    (S.TBool, S.If (expect_bool env a, expect_bool env b, bfalse))
  | EBinop (Or, a, b) ->
    (S.TBool, S.If (expect_bool env a, btrue, expect_bool env b))
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
  | ELam (ps, body) -> params env ps (fun env -> desugar env body)
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
  | ERcd ((l, fe) :: rest as fs) ->
    check_no_duplicates e.loc "record" (List.map fst fs);
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
  (* `;` binds nothing: its right operand cannot see the left one. *)
  | EMerge (MNon, a, b) ->
    let ta, ca = desugar env a in
    let tb, cb = desugar env b in
    (S.TAnd (ta, tb), S.Nmrg (ca, cb))
  | EMerge (MDep, a, b) ->
    let ta, ca = desugar env a in
    let x, env' = bind_fields F.mrg ta env in
    let tb, cb = desugar env' b in
    (S.TAnd (ta, tb), S.Mrg (x, ca, cb))
  | ELet (b, body) ->
    let x = b.b_bind.bd_name in
    let vt, cv = binding env b in
    let bt, cb = desugar (bind F.letb x vt env) body in
    (bt, S.Letb (x, cv, vt, cb))
  | EOpen (m, body) ->
    let mt, cm = desugar env m in
    let x, env' = open_slot env m.loc mt in
    let bt, cb = desugar env' body in
    (bt, S.Openm (x, S.Lrec (open_label, cm), cb))
  | EBox (m, body) ->
    let mt, cm = desugar env m in
    let bt, cb = desugar { env with slots = F.box env.slots; base = mt } body in
    (bt, S.Box (cm, cb))
  | ECase (scrut, x, e1, y, e2) -> (
    let ts, cs = desugar env scrut in
    match ts with
    | S.TOr (a, b) ->
      let branch (bnd : binder) t body =
        desugar (bind F.case_branch bnd.bd_name t env) body
      in
      let t1, c1 = branch x a e1 in
      let t2, c2 = branch y b e2 in
      if t1 <> t2 then mismatch e2.loc "the branches of `case` disagree" t1 t2;
      (t1, S.Case (cs, x.bd_name, c1, y.bd_name, c2))
    | _ ->
      err scrut.loc "`case` expects a union type, got %s" (P.typ_to_string ts))
  | EStruct (sb, ds) ->
    let env0 = match sb with Sandboxed -> reset env | Open -> env in
    let t, c = structure env0 ds in
    (t, S.Mstruct (conv_sandbox sb, c))
  | EFunctor (sb, ps, body) -> functors env sb ps body
  | ELink (k, m, f) -> link env e.loc k m f
  | EMatch _ -> err e.loc "internal: `match` survived Adt.expand"

and expect_bool env e =
  let t, c = desugar env e in
  if t <> S.TBool then mismatch e.loc "condition" S.TBool t;
  c

(* Curried parameters: each one extends the context left to right, and the term
   nests to match. Shared by `fun`, by `let f x y = ...`, and by the extra
   parameters of a `let rec`. *)
and params env ps k =
  match ps with
  | [] -> k env
  | p :: rest ->
    let x = p.p_bind.bd_name in
    let a = conv_typ env p.p_typ in
    let bt, cb = params (bind F.lam x a env) rest k in
    (S.TArr (a, bt), S.Lam (x, a, cb))

(* An `open` reaches its subject's fields, so a subject with no labels brings
   nothing into scope — say so here rather than reporting each use as unbound. *)
and open_slot env loc mt =
  if labels_of mt = [] then
    err loc
      "cannot determine the fields of this expression, so `open` does not know \
       what it brings into scope; add a type annotation";
  bind_fields F.openm mt env

(* Ascription has no core counterpart; it is a check here, and it is what
   supplies the types `Inl`, `Inr` and `Fold` cannot infer. *)
and ascribe env loc (inner : exp) (ty : S.typ) =
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

(* Only the outermost functor carries the sandbox flag; the curried ones inside
   it inherit an already-sandboxed context. *)
and functors env sb ps body =
  match ps with
  | [] -> desugar env body
  | p :: rest ->
    let outer = match sb with Sandboxed -> reset env | Open -> env in
    let x = p.p_bind.bd_name in
    let a = conv_typ outer p.p_typ in
    let bt, cb = functors (bind F.lam x a outer) Open rest body in
    (S.TSig (S.TyArrM (a, S.TyIntf bt)), S.Mfunctor (conv_sandbox sb, x, a, cb))

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

and binding env (b : binding) : S.typ * S.named =
  if b.b_rec then recursive_binding env b
  else
    params env b.b_params (fun env ->
      let bt, cb = desugar env b.b_exp in
      (match b.b_ann with
       | Some t ->
         let want = conv_typ env t in
         if bt <> want then mismatch b.b_exp.loc "annotation" want bt
       | None -> ());
      (bt, cb))

(* `Flam (f, x, A, B, body)` types its body under `(ctx & (A -> B)) & A`, so the
   recursive name sits *below* the parameters. Extra parameters become plain
   lambdas inside it. *)
and recursive_binding env (b : binding) : S.typ * S.named =
  let f = b.b_bind.bd_name in
  let ret =
    match b.b_ann with
    | Some t -> conv_typ env t
    | None ->
      err b.b_bind.bd_loc
        "'let rec %s' needs a return type annotation: the recursive call has \
         to be typed before the body is checked" f
  in
  match b.b_params with
  | [] -> err b.b_bind.bd_loc "'let rec %s' needs at least one parameter" f
  | p :: rest ->
    let x = p.p_bind.bd_name in
    let a = conv_typ env p.p_typ in
    let cod =
      List.fold_right (fun q acc -> S.TArr (conv_typ env q.p_typ, acc)) rest ret
    in
    let self = S.TArr (a, cod) in
    let inner =
      { env with
        slots = F.flam ~self:(Named (f, self)) ~arg:(Named (x, a)) env.slots }
    in
    let _, body =
      params inner rest (fun env ->
        let bt, cb = desugar env b.b_exp in
        if bt <> ret then mismatch b.b_exp.loc "recursive function body" ret bt;
        (bt, cb))
    in
    (self, S.Flam (f, x, a, cod, body))

(* The value a `let` or `module` declaration contributes, under whatever
   context the chain it belongs to has built up. *)
and declared env (d : decl) =
  match d.it with
  | DLet b ->
    let t, c = binding env b in
    (b.b_bind.bd_name, t, c)
  | DModule (bn, me) ->
    let t, c = desugar env me in
    (bn.bd_name, t, c)
  | _ -> assert false

(* A structure is a left-nested *dependent* merge chain, so each declaration
   sees one extra slot holding everything declared before it — one slot that
   widens, never one per declaration. *)
and structure env (ds : decl list) : S.typ * S.named =
  let rec go env chain ds =
    let x, here =
      match chain with
      | None -> ("", env)
      | Some (t, _) -> bind_fields F.mrg t env
    in
    let add (t, c) =
      match chain with
      | None -> (t, c)
      | Some (pt, pc) -> (S.TAnd (pt, t), S.Mrg (x, pc, c))
    in
    match ds with
    | [] -> ( match chain with Some tc -> tc | None -> (S.TTop, S.Unit))
    | d :: rest -> (
      match d.it with
      | DType (b, t) ->
        go { env with aliases = (b.bd_name, conv_typ here t) :: env.aliases }
          chain rest
      | DAdt _ -> err d.loc "internal: ADT declaration survived Adt.expand"
      | DLet _ | DModule _ ->
        let l, vt, cv = declared here d in
        go env (Some (add (S.TRcd (l, vt), S.Lrec (l, cv)))) rest
      | DOpen m ->
        (* The declarations after an `open` become its body and start a fresh
           chain on top of the opened slot. *)
        let mt, cm = desugar here m in
        let o, inner = open_slot here m.loc mt in
        let rt, rc = go inner None rest in
        add (rt, S.Openm (o, S.Lrec (open_label, cm), rc)))
  in
  check_no_duplicate_decls "structure" ds;
  go env None ds

(* ---------------- programs ----------------

   Top-level declarations chain with `Letb`, not with the dependent merge a
   struct uses, so each one binds a plain name at index 0. *)

(* A program is its `main` binding, matching how a linked unit is run; with no
   `main` it evaluates to the record of everything it binds at the top level. *)
let main_exp (p : Ast.program) : exp =
  match p.main with
  | Some e -> e
  | None ->
    let occ n = mk dummy_loc (EVar n) in
    let names = List.filter_map name_of_decl p.decls in
    if List.mem "main" names then occ "main"
    else mk dummy_loc (ERcd (List.map (fun n -> (n, occ n)) names))

let desugar_program (p : Ast.program) : S.typ * S.named =
  (match p.imports with
   | [] -> ()
   | (b, _) :: _ ->
     err b.bd_loc "imports make this file a unit; compile it with -c");
  check_no_duplicate_decls "program" p.decls;
  let rec go env ds =
    match ds with
    | [] -> desugar env (main_exp p)
    | d :: rest -> (
      match d.it with
      | DType (b, t) ->
        go { env with aliases = (b.bd_name, conv_typ env t) :: env.aliases } rest
      | DAdt _ -> err d.loc "internal: ADT declaration survived Adt.expand"
      | DLet _ | DModule _ ->
        let x, vt, cv = declared env d in
        let bt, cb = go (bind F.letb x vt env) rest in
        (bt, S.Letb (x, cv, vt, cb))
      | DOpen m ->
        let mt, cm = desugar env m in
        let o, inner = open_slot env m.loc mt in
        let bt, cb = go inner rest in
        (bt, S.Openm (o, S.Lrec (open_label, cm), cb)))
  in
  go empty_env p.decls
