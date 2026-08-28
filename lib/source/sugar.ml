(* Desugaring: named surface AST -> named λSCE.

   Resolves names and synthesizes types in one pass, because each needs the
   other: a name is a slot of the context or an unambiguous field of one, and
   `Elab.srlookup_opt` on the type just synthesized settles which. Types are
   synthesized, never *checked* — Elab checks the term this builds. What is
   rejected here is what would otherwise make the translation itself
   meaningless: an unbound name, or a form whose type has the wrong shape to
   continue from. lib/sce/debruijn.ml turns each name into its index. *)

open Ast
module S = Sce_core.Ast
module E = Sce_core.Elab
module P = Sce_core.Pretty

exception Error of string * loc

let err loc fmt = Printf.ksprintf (fun s -> raise (Error (s, loc))) fmt

(* Elab's judgement helpers raise their own exception. *)
let lift loc f = try f () with E.Elab_error m -> raise (Error (m, loc))

(* Left-nested chain of a non-empty list. *)
let fold1 f = function [] -> None | x :: xs -> Some (List.fold_left f x xs)

(* A duplicate label makes *both* copies unreachable: srlookup refuses it. *)
let check_unique what items =
  ignore
    (List.fold_left
       (fun seen (l, loc) ->
         if List.mem l seen then
           err loc "duplicate field '%s' in this %s; it would be unreachable" l
             what
         else l :: seen)
       [] items)

let decl_labels ds =
  List.filter_map (fun d -> Option.map (fun l -> (l, d.loc)) (name_of_decl d)) ds

(* ---------------- the context ---------------- *)

(* A binder, reached by its name; or an anonymous merge/open/struct slot with a
   generated `%`-name, reached by the labels of its type. Both take an index. *)
type slot = { name : string; typ : S.typ; fields : bool }

module F = Sce_core.Frames.Make (struct
  type t = slot
end)

type env = {
  slots : F.env;
  base : S.typ;                    (* what a box or sandbox installed underneath *)
  mus : string list;               (* mu binders in scope, innermost first *)
  aliases : (string * S.typ) list; (* alias bodies, resolved and closed *)
}

let empty_env = { slots = F.empty; base = S.TTop; mus = []; aliases = [] }

(* `base` keeps ctx exact rather than a left-nested approximation. *)
let ctx env =
  List.fold_left (fun acc s -> S.TAnd (acc, s.typ)) env.base (List.rev env.slots)

let reset env = { env with slots = F.sandbox env.slots; base = S.TTop }

(* `push` is the Frames rule for the form, so the slot lands where Debruijn
   will count it. `%` cannot start a surface identifier, and there is one slot
   per depth, so a generated name is unique wherever it is in scope. *)
let bind push x t env =
  { env with slots = push { name = x; typ = t; fields = false } env.slots }

let bind_fields push t env =
  let x = "%" ^ string_of_int (List.length env.slots) in
  (x, { env with slots = push { name = x; typ = t; fields = true } env.slots })

(* The innermost slot providing x. Ambiguity is not a match. *)
let find env x =
  let hit s =
    if String.equal s.name x then Some (S.Var x, s.typ)
    else if s.fields then
      Option.map
        (fun t -> (S.Rproj (S.Var s.name, x), t))
        (E.srlookup_opt s.typ x)
    else None
  in
  List.find_map hit env.slots

(* ---------------- types ---------------- *)

let rec conv_typ env (t : typ) : S.typ =
  let conv = conv_typ env in
  match t.it with
  | TInt -> S.TInt
  | TBool -> S.TBool
  | TString -> S.TString
  | TTop -> S.TTop
  | TArr (a, b) -> S.TArr (conv a, conv b)
  | TAnd (a, b) -> S.TAnd (conv a, conv b)
  | TOr (a, b) -> S.TOr (conv a, conv b)
  (* `A => B => C` curries: Mfunctor's result is an interface that is itself a
     signature, never a nested TyArrM. *)
  | TSig (a, b) -> S.TSig (S.TyArrM (conv a, S.TyIntf (conv b)))
  | TMu (b, body) -> S.TMu (conv_typ { env with mus = b.bd_name :: env.mus } body)
  | TRcd fs ->
    check_unique "record type" (List.map (fun (l, _) -> (l, t.loc)) fs);
    Option.value ~default:S.TTop
      (fold1
         (fun a b -> S.TAnd (a, b))
         (List.map (fun (l, ft) -> S.TRcd (l, conv ft)) fs))
  | TVar a -> (
    match List.find_index (String.equal a) env.mus with
    | Some i -> S.TVar i
    (* Alias bodies are closed, so they drop in under any mu unshifted. *)
    | None -> (
      match List.assoc_opt a env.aliases with
      | Some rt -> rt
      | None -> err t.loc "unbound type name '%s'" a))

(* A type with nothing in scope: a .scei interface, aliases already expanded. *)
let conv_typ_closed (t : typ) : S.typ = conv_typ empty_env t

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

(* The label an `open` subject is wrapped in, so Openm sees a record. *)
let open_label = "%open"

(* ---------------- expressions ---------------- *)

let rec desugar env (e : exp) : S.typ * S.named =
  let only e = snd (desugar env e) in
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
    match desugar env e1 with
    | S.TMu body, c -> (E.unfold_mu body, S.Unfold c)
    | t, _ ->
      err e1.loc "`unfold` expects a recursive type, got %s" (P.typ_to_string t))
  (* `&&`, `||`, `not` are short-circuiting sugar for `if`; unary `-` for
     subtraction. None reach the core. *)
  | EBinop (And, a, b) -> (S.TBool, S.If (only a, only b, bfalse))
  | EBinop (Or, a, b) -> (S.TBool, S.If (only a, btrue, only b))
  | EUnop (Not, a) -> (S.TBool, S.If (only a, bfalse, btrue))
  | EUnop (Neg, a) -> (S.TInt, S.Binop (S.Sub, S.Lit (S.Int 0), only a))
  | EBinop (op, a, b) ->
    let ta, ca = desugar env a in
    let tb, cb = desugar env b in
    ( lift e.loc (fun () -> E.typ_of_binop (conv_binop op) ta tb),
      S.Binop (conv_binop op, ca, cb) )
  (* No subtyping, so no join to compute: Elab makes the branches agree. *)
  | EIf (c, t, f) ->
    let cc = only c in
    let tt, ct = desugar env t in
    (tt, S.If (cc, ct, only f))
  | ELam (ps, body) -> params env ps (fun env -> desugar env body)
  (* The head's type is what says whether this is a function or a functor. *)
  | EApp (f, a) -> (
    let tf, cf = desugar env f in
    match tf with
    | S.TArr (_, cod) -> (cod, S.App (cf, only a))
    | S.TSig (S.TyArrM (_, S.TyIntf cod)) -> (cod, S.Mapp (cf, only a))
    | _ ->
      err f.loc "this is applied to an argument but has type %s"
        (P.typ_to_string tf))
  (* Fields are independent, so a record is a non-dependent merge chain. *)
  | ERcd fs ->
    check_unique "record" (List.map (fun (l, _) -> (l, e.loc)) fs);
    let field (l, fe) =
      let t, c = desugar env fe in
      (S.TRcd (l, t), S.Lrec (l, c))
    in
    Option.value ~default:(S.TTop, S.Unit)
      (fold1
         (fun (ta, ca) (tb, cb) -> (S.TAnd (ta, tb), S.Nmrg (ca, cb)))
         (List.map field fs))
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
    let x, env = bind_fields F.mrg ta env in
    let tb, cb = desugar env b in
    (S.TAnd (ta, tb), S.Mrg (x, ca, cb))
  | ELet (b, body) ->
    let x = b.b_bind.bd_name in
    let vt, cv = binding env b in
    let bt, cb = desugar (bind F.letb x vt env) body in
    (bt, S.Letb (x, cv, vt, cb))
  | EOpen (m, body) ->
    let subj, x, env = opening env m in
    let bt, cb = desugar env body in
    (bt, S.Openm (x, subj, cb))
  | EBox (m, body) ->
    let mt, cm = desugar env m in
    let bt, cb = desugar { env with slots = F.box env.slots; base = mt } body in
    (bt, S.Box (cm, cb))
  | ECase (scrut, x, e1, y, e2) -> (
    match desugar env scrut with
    | S.TOr (a, b), cs ->
      let branch (bnd : binder) t body =
        desugar (bind F.case_branch bnd.bd_name t env) body
      in
      let t1, c1 = branch x a e1 in
      (t1, S.Case (cs, x.bd_name, c1, y.bd_name, snd (branch y b e2)))
    | ts, _ ->
      err scrut.loc "`case` expects a union type, got %s" (P.typ_to_string ts))
  | EStruct (sb, ds) ->
    let t, c = structure (match sb with Sandboxed -> reset env | Open -> env) ds in
    (t, S.Mstruct (conv_sandbox sb, c))
  | EFunctor (sb, ps, body) -> functors env sb ps body
  | ELink (k, m, f) -> link env e.loc k m f
  | EMatch _ -> err e.loc "internal: `match` survived Adt.expand"

(* Curried parameters extend the context left to right; the term nests to
   match. Shared by `fun`, `let f x y`, and a `let rec`'s extra parameters. *)
and params env ps k =
  match ps with
  | [] -> k env
  | p :: rest ->
    let x = p.p_bind.bd_name in
    let a = conv_typ env p.p_typ in
    let bt, cb = params (bind F.lam x a env) rest k in
    (S.TArr (a, bt), S.Lam (x, a, cb))

(* `open m`: the wrapped subject, the slot's name, and the extended env. A
   subject with no labels brings nothing into scope. *)
and opening env (m : exp) =
  let mt, cm = desugar env m in
  if E.record_fields mt = [] then
    err m.loc
      "cannot determine the fields of this expression, so `open` does not know \
       what it brings into scope; add a type annotation";
  let x, env = bind_fields F.openm mt env in
  (S.Lrec (open_label, cm), x, env)

(* Ascription has no core counterpart: it supplies the types Inl, Inr and Fold
   cannot infer, and hands Elab something to check the term against. *)
and ascribe env loc (inner : exp) (ty : S.typ) =
  let payload a node = (ty, node (snd (desugar env a))) in
  match (inner.it, ty) with
  | EInl a, S.TOr (_, r) -> payload a (fun c -> S.Inl (r, c))
  | EInr a, S.TOr (l, _) -> payload a (fun c -> S.Inr (l, c))
  | (EInl _ | EInr _), _ ->
    err loc "an injection must be ascribed a union type, got %s"
      (P.typ_to_string ty)
  | EFold a, S.TMu body -> payload a (fun c -> S.Fold (body, c))
  | EFold _, _ ->
    err loc "`fold` must be ascribed a recursive type, got %s"
      (P.typ_to_string ty)
  | _ -> (ty, snd (desugar env inner))

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
  match desugar env f with
  | S.TSig (S.TyArrM (_, S.TyIntf result)), cf ->
    ( S.TAnd (mt, result),
      match k with LOne -> S.Mlink (cm, cf) | LAll -> S.Mlinkn (cm, cf) )
  | ft, _ ->
    err loc "the target of `link` must be a functor, but has type %s"
      (P.typ_to_string ft)

(* An annotation is reported rather than checked, so Elab's Letb rule is what
   compares it against the bound term. *)
and binding env (b : binding) : S.typ * S.named =
  if b.b_rec then recursive_binding env b
  else
    params env b.b_params (fun env ->
      let bt, cb = desugar env b.b_exp in
      ((match b.b_ann with Some t -> conv_typ env t | None -> bt), cb))

(* Flam types its body under `(ctx & (A -> B)) & A`, so the recursive name sits
   below the parameters; extra parameters become plain lambdas inside it. *)
and recursive_binding env (b : binding) : S.typ * S.named =
  let f = b.b_bind.bd_name in
  match (b.b_ann, b.b_params) with
  | None, _ ->
    err b.b_bind.bd_loc
      "'let rec %s' needs a return type annotation: the recursive call has to \
       be typed before the body is checked" f
  | _, [] -> err b.b_bind.bd_loc "'let rec %s' needs at least one parameter" f
  | Some ann, p :: rest ->
    let ret = conv_typ env ann in
    let x = p.p_bind.bd_name in
    let a = conv_typ env p.p_typ in
    let cod =
      List.fold_right (fun q acc -> S.TArr (conv_typ env q.p_typ, acc)) rest ret
    in
    let self = S.TArr (a, cod) in
    let slot n t = { name = n; typ = t; fields = false } in
    let inner =
      { env with slots = F.flam ~self:(slot f self) ~arg:(slot x a) env.slots }
    in
    let _, body = params inner rest (fun env -> (ret, snd (desugar env b.b_exp))) in
    (self, S.Flam (f, x, a, cod, body))

and declared env (d : decl) =
  match d.it with
  | DLet b -> (b.b_bind.bd_name, binding env b)
  | DModule (bn, me) -> (bn.bd_name, desugar env me)
  | _ -> assert false

(* A struct is a left-nested *dependent* merge chain: each declaration is
   desugared under one slot holding everything before it — one slot that
   widens, never one per declaration. *)
and structure env (ds : decl list) : S.typ * S.named =
  let step env = function
    | None -> (env, fun tc -> tc)
    | Some (pt, pc) ->
      let x, here = bind_fields F.mrg pt env in
      (here, fun (t, c) -> (S.TAnd (pt, t), S.Mrg (x, pc, c)))
  in
  let rec go env chain ds =
    let here, add = step env chain in
    match ds with
    | [] -> ( match chain with Some tc -> tc | None -> (S.TTop, S.Unit))
    | d :: rest -> (
      match d.it with
      | DType (b, t) ->
        go { env with aliases = (b.bd_name, conv_typ here t) :: env.aliases }
          chain rest
      | DLet _ | DModule _ ->
        let l, (vt, cv) = declared here d in
        go env (Some (add (S.TRcd (l, vt), S.Lrec (l, cv)))) rest
      (* The declarations after an `open` are its body, on a fresh chain. *)
      | DOpen m ->
        let subj, o, inner = opening here m in
        let rt, rc = go inner None rest in
        add (rt, S.Openm (o, subj, rc))
      | DAdt _ -> err d.loc "internal: ADT declaration survived Adt.expand")
  in
  check_unique "structure" (decl_labels ds);
  go env None ds

(* Top-level declarations chain with Letb, not with a struct's dependent merge,
   so each binds a plain name at index 0. With no `main`, the program is the
   record of everything it binds — matching how a linked unit is run. *)
let desugar_program (p : Ast.program) : S.typ * S.named =
  (match p.imports with
   | [] -> ()
   | (b, _) :: _ ->
     err b.bd_loc "imports make this file a unit; compile it with -c");
  check_unique "program" (decl_labels p.decls);
  let main =
    match p.main with
    | Some e -> e
    | None ->
      let occ n = mk dummy_loc (EVar n) in
      let names = List.filter_map name_of_decl p.decls in
      if List.mem "main" names then occ "main"
      else mk dummy_loc (ERcd (List.map (fun n -> (n, occ n)) names))
  in
  let rec go env ds =
    match ds with
    | [] -> desugar env main
    | d :: rest -> (
      match d.it with
      | DType (b, t) ->
        go { env with aliases = (b.bd_name, conv_typ env t) :: env.aliases } rest
      | DLet _ | DModule _ ->
        let x, (vt, cv) = declared env d in
        let bt, cb = go (bind F.letb x vt env) rest in
        (bt, S.Letb (x, cv, vt, cb))
      | DOpen m ->
        let subj, o, inner = opening env m in
        let bt, cb = go inner rest in
        (bt, S.Openm (o, subj, cb))
      | DAdt _ -> err d.loc "internal: ADT declaration survived Adt.expand")
  in
  go empty_env p.decls
