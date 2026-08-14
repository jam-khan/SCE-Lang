(* Scope resolution: named surface AST -> de Bruijn indexed surface AST.

   Purely syntactic — no types are involved. Every `EVar "x"` becomes a `path`,
   every `TVar "a"` becomes a de Bruijn index, and every type alias is expanded.
   The context discipline it indexes into lives in Frames, which Sugar shares. *)

open Ast

exception Error of string * loc

let err loc fmt = Printf.ksprintf (fun s -> raise (Error (s, loc))) fmt

(* ---------------- shapes ----------------

   A name can be bound directly, or it can be a *field* of a slot whose
   contents are in scope (a struct's earlier declarations, or an `open`).
   Resolving the second kind needs the slot's labels, so every binding carries
   a shape, read off syntax alone. *)

type shape =
  | SOpaque
  | SRcd of (string * shape) list
  | SFun of shape
  | SOr  of shape * shape

let merge_shape a b =
  match (a, b) with
  | SRcd f1, SRcd f2 -> SRcd (f1 @ f2)
  | SRcd _, _ -> a
  | _, SRcd _ -> b
  | _ -> SOpaque

(* Works on named and indexed types alike: it never inspects a type variable. *)
let rec shape_of_typ : 'a. 'a typ -> shape =
  fun (type a) (t : a typ) ->
   match t.it with
   | TRcd fs -> SRcd (List.map (fun (l, ft) -> (l, shape_of_typ ft)) fs)
   | TAnd (a, b) -> merge_shape (shape_of_typ a) (shape_of_typ b)
   | TOr (a, b) -> SOr (shape_of_typ a, shape_of_typ b)
   | TArr (_, b) | TSig (_, b) -> SFun (shape_of_typ b)
   | TInt | TBool | TString | TTop | TVar _ | TMu _ -> SOpaque

let fun_result = function SFun s -> s | _ -> SOpaque

let field_shape s l =
  match s with
  | SRcd fs -> Option.value ~default:SOpaque (List.assoc_opt l fs)
  | _ -> SOpaque

(* A slot we cannot see into still occupies an index, so it is pushed as an
   empty field set rather than skipped. *)
let fields_of = function SRcd fs -> fs | _ -> []

(* ---------------- environment ---------------- *)

type frame =
  | FBind of string * shape
  | FFields of (string * shape) list

module F = Frames.Make (struct
  type t = frame
end)

type env = {
  frames : F.env;
  mus : string list;                 (* mu binders in scope, innermost first *)
  aliases : (string * int typ) list; (* alias bodies, already resolved and closed *)
}

let empty_env = { frames = F.empty; mus = []; aliases = [] }

let rec find frames i x =
  match frames with
  | [] -> None
  | FBind (y, s) :: rest ->
    if String.equal y x then Some (PIdx i, s) else find rest (i + 1) x
  | FFields fs :: rest -> (
    match List.assoc_opt x fs with
    | Some s -> Some (PField (i, x), s)
    | None -> find rest (i + 1) x)

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

let rec resolve_typ env (t : string typ) : int typ =
  let nd it = { it; loc = t.loc } in
  match t.it with
  | TInt -> nd TInt
  | TBool -> nd TBool
  | TString -> nd TString
  | TTop -> nd TTop
  | TVar a -> (
    let rec index i = function
      | [] -> None
      | b :: rest -> if String.equal b a then Some i else index (i + 1) rest
    in
    match index 0 env.mus with
    | Some i -> nd (TVar i)
    | None -> (
      (* Alias bodies are resolved with an empty mu stack, so they are closed
         and can be dropped in under any number of mu binders unshifted. *)
      match List.assoc_opt a env.aliases with
      | Some rt -> rt
      | None -> err t.loc "unbound type name '%s'" a))
  | TArr (a, b) -> nd (TArr (resolve_typ env a, resolve_typ env b))
  | TAnd (a, b) -> nd (TAnd (resolve_typ env a, resolve_typ env b))
  | TOr (a, b) -> nd (TOr (resolve_typ env a, resolve_typ env b))
  | TSig (a, b) -> nd (TSig (resolve_typ env a, resolve_typ env b))
  | TRcd fs ->
    check_no_duplicates t.loc "record type" (List.map fst fs);
    nd (TRcd (List.map (fun (l, ft) -> (l, resolve_typ env ft)) fs))
  | TMu (b, body) ->
    nd (TMu (b, resolve_typ { env with mus = b.bd_name :: env.mus } body))

let resolve_typ_opt env = Option.map (resolve_typ env)

(* ---------------- named-level alias expansion ----------------

   A .scei interface is aliases + a type, resolved *before* it meets the
   importing file's scope — so its aliases are expanded syntactically here,
   producing a self-contained named type. A mu binder of the same name
   shadows an alias inside its body. *)

let rec subst_tname (name : string) (body : string typ) (t : string typ) : string typ =
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

let expand_aliases (aliases : (binder * string typ) list) (t : string typ) : string typ =
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

(* ---------------- expressions ---------------- *)

let rec resolve_exp env (e : (string, string) exp) : (path, int) exp * shape =
  let nd it = { it; loc = e.loc } in
  let only env x = fst (resolve_exp env x) in
  match e.it with
  | EVar x -> (
    match find env.frames 0 x with
    | Some (p, s) -> (nd (EVar p), s)
    | None -> err e.loc "unbound variable '%s'" x)
  | ELit l -> (nd (ELit l), SOpaque)
  | EUnit -> (nd EUnit, SOpaque)
  | EQuery -> (nd EQuery, SOpaque)
  | EAnnot (e1, t) ->
    let ce1 = only env e1 in
    let ct = resolve_typ env t in
    (nd (EAnnot (ce1, ct)), shape_of_typ ct)
  | EBinop (op, a, b) -> (nd (EBinop (op, only env a, only env b)), SOpaque)
  | EUnop (op, a) -> (nd (EUnop (op, only env a)), SOpaque)
  | EIf (c, t, f) ->
    let cc = only env c in
    let ct, st = resolve_exp env t in
    let cf = only env f in
    (nd (EIf (cc, ct, cf)), st)
  | ELam (ps, body) ->
    let cps, env' = resolve_params env ps in
    let cb, sb = resolve_exp env' body in
    (nd (ELam (cps, cb)), List.fold_left (fun acc _ -> SFun acc) sb ps)
  | EApp (f, a) ->
    let cf, sf = resolve_exp env f in
    (nd (EApp (cf, only env a)), fun_result sf)
  | ERcd fs ->
    check_no_duplicates e.loc "record" (List.map fst fs);
    let resolved =
      List.map
        (fun (l, fe) ->
          let ce, s = resolve_exp env fe in
          ((l, ce), (l, s)))
        fs
    in
    (nd (ERcd (List.map fst resolved)), SRcd (List.map snd resolved))
  | EField (b, l) ->
    let cb, sb = resolve_exp env b in
    (nd (EField (cb, l)), field_shape sb l)
  | EIndex (b, n) -> (nd (EIndex (only env b, n)), SOpaque)
  | EMerge (k, a, b) ->
    let ca, sa = resolve_exp env a in
    let frames =
      match k with
      | MNon -> F.nmrg (FFields (fields_of sa)) env.frames
      | MDep -> F.mrg (FFields (fields_of sa)) env.frames
    in
    let cb, sb = resolve_exp { env with frames } b in
    (nd (EMerge (k, ca, cb)), merge_shape sa sb)
  | ELet (b, body) ->
    let cb, s = resolve_binding env b in
    let frames = F.letb (FBind (b.b_bind.bd_name, s)) env.frames in
    let cbody, sbody = resolve_exp { env with frames } body in
    (nd (ELet (cb, cbody)), sbody)
  | EOpen (m, body) ->
    let cm, sm = resolve_exp env m in
    let frames = F.openm (FFields (opened_fields m.loc sm)) env.frames in
    let cbody, sbody = resolve_exp { env with frames } body in
    (nd (EOpen (cm, cbody)), sbody)
  | EBox (m, body) ->
    let cm = only env m in
    let cbody, sbody = resolve_exp { env with frames = F.box env.frames } body in
    (nd (EBox (cm, cbody)), sbody)
  | EInl a -> (nd (EInl (only env a)), SOpaque)
  | EInr a -> (nd (EInr (only env a)), SOpaque)
  | EFold a -> (nd (EFold (only env a)), SOpaque)
  | EUnfold a -> (nd (EUnfold (only env a)), SOpaque)
  | ECase (scrut, x, e1, y, e2) ->
    let cs, ss = resolve_exp env scrut in
    let sl, sr = match ss with SOr (l, r) -> (l, r) | _ -> (SOpaque, SOpaque) in
    let branch bnd s body =
      let frames = F.case_branch (FBind (bnd.bd_name, s)) env.frames in
      resolve_exp { env with frames } body
    in
    let c1, s1 = branch x sl e1 in
    let c2, _ = branch y sr e2 in
    (nd (ECase (cs, x, c1, y, c2)), s1)
  | EStruct (sb, ds) ->
    let frames = match sb with Sandboxed -> F.sandbox env.frames | Open -> env.frames in
    let cds, fields = resolve_struct { env with frames } ds in
    (nd (EStruct (sb, cds)), SRcd fields)
  | EFunctor (sb, ps, body) ->
    let frames = match sb with Sandboxed -> F.sandbox env.frames | Open -> env.frames in
    let cps, env' = resolve_params { env with frames } ps in
    let cb, sbody = resolve_exp env' body in
    (nd (EFunctor (sb, cps, cb)), List.fold_left (fun acc _ -> SFun acc) sbody ps)
  | ELink (k, m, f) ->
    let cm, sm = resolve_exp env m in
    let cf, sf = resolve_exp env f in
    (* Mlink yields the merge of the module with the functor's result. *)
    (nd (ELink (k, cm, cf)), merge_shape sm (fun_result sf))
  | EMatch _ -> err e.loc "internal: `match` survived Adt.expand"

and opened_fields loc = function
  | SRcd fs -> fs
  | _ ->
    err loc
      "cannot determine the fields of this expression, so `open` does not know \
       what it brings into scope; add a type annotation"

and resolve_params env ps =
  let cps, env =
    List.fold_left
      (fun (acc, env) p ->
        let pt = resolve_typ env p.p_typ in
        let frames = F.lam (FBind (p.p_bind.bd_name, shape_of_typ pt)) env.frames in
        ({ p_bind = p.p_bind; p_typ = pt } :: acc, { env with frames }))
      ([], env) ps
  in
  (List.rev cps, env)

and resolve_binding env (b : (string, string) binding) :
    (path, int) binding * shape =
  let ann = resolve_typ_opt env b.b_ann in
  let shape_of_body body_shape =
    let ret = match ann with Some t -> shape_of_typ t | None -> body_shape in
    List.fold_left (fun acc _ -> SFun acc) ret b.b_params
  in
  if b.b_rec then begin
    if b.b_params = [] then
      err b.b_bind.bd_loc
        "'let rec %s' needs at least one parameter: it elaborates to a \
         recursive function" b.b_bind.bd_name;
    (* Flam pushes the function itself, then the argument, so the parameters
       sit at lower indices than the recursive name. *)
    let self = shape_of_body SOpaque in
    let frames = F.push (FBind (b.b_bind.bd_name, self)) env.frames in
    let cps, env' = resolve_params { env with frames } b.b_params in
    let cbody = fst (resolve_exp env' b.b_exp) in
    ({ b_rec = true; b_bind = b.b_bind; b_params = cps; b_ann = ann; b_exp = cbody }, self)
  end
  else begin
    let cps, env' = resolve_params env b.b_params in
    let cbody, sbody = resolve_exp env' b.b_exp in
    ( { b_rec = false; b_bind = b.b_bind; b_params = cps; b_ann = ann; b_exp = cbody },
      shape_of_body sbody )
  end

(* A struct body is a left-nested *dependent* merge chain, so every declaration
   after the first sees exactly one extra slot holding all the fields declared
   before it. One frame is pushed and then widened — never one frame per
   declaration. *)
and resolve_struct env (ds : (string, string) decl list) :
    (path, int) decl list * (string * shape) list =
  let rec go env chain acc ds =
    let framed env =
      if chain = [] then env
      else { env with frames = F.mrg (FFields chain) env.frames }
    in
    match ds with
    | [] -> (List.rev acc, chain)
    | d :: rest -> (
      let here = framed env in
      match d.it with
      | DType (b, t) ->
        let rt = resolve_typ here t in
        let env = { env with aliases = (b.bd_name, rt) :: env.aliases } in
        go env chain ({ it = DType (b, rt); loc = d.loc } :: acc) rest
      | DLet bnd ->
        let cb, s = resolve_binding here bnd in
        go env
          (chain @ [ (bnd.b_bind.bd_name, s) ])
          ({ it = DLet cb; loc = d.loc } :: acc)
          rest
      | DModule (b, me) ->
        let cm, s = resolve_exp here me in
        go env
          (chain @ [ (b.bd_name, s) ])
          ({ it = DModule (b, cm); loc = d.loc } :: acc)
          rest
      | DOpen m ->
        let cm, sm = resolve_exp here m in
        let frames = F.openm (FFields (opened_fields m.loc sm)) here.frames in
        (* The remaining declarations become the Openm body and start a fresh
           chain on top of the opened slot. *)
        let crest, rest_fields = go { here with frames } [] [] rest in
        ( List.rev ({ it = DOpen cm; loc = d.loc } :: acc) @ crest,
          chain @ rest_fields )
      | DAdt _ -> err d.loc "internal: ADT declaration survived Adt.expand")
  in
  check_no_duplicate_decls "structure" ds;
  go env [] [] ds

(* ---------------- programs ----------------

   Top-level declarations chain with `Letb`, not with the dependent merge a
   struct uses, so each one binds a plain name at index 0. *)

(* A program is its `main` binding, matching how a linked unit is run; with no
   `main` it evaluates to the record of everything it binds at the top level.
   Building it here keeps all name resolution in one pass. *)
let default_main env (p : Ast.named) : (path, int) exp =
  match p.main with
  | Some e -> fst (resolve_exp env e)
  | None ->
    let loc = dummy_loc in
    let names = List.filter_map name_of_decl p.decls in
    let occurrence name =
      match find env.frames 0 name with
      | Some (path, _) -> { it = EVar path; loc }
      | None -> err loc "unbound variable '%s'" name
    in
    if List.mem "main" names then occurrence "main"
    else
      { it = ERcd (List.map (fun n -> (n, occurrence n)) names); loc }

let resolve (p : Ast.named) : Ast.indexed =
  (match p.imports with
   | [] -> ()
   | (b, _) :: _ ->
     err b.bd_loc "imports make this file a unit; compile it with -c");
  check_no_duplicate_decls "program" p.decls;
  let rec go env acc ds =
    match ds with
    | [] -> (List.rev acc, default_main env p)
    | d :: rest -> (
      match d.it with
      | DType (b, t) ->
        let rt = resolve_typ env t in
        go
          { env with aliases = (b.bd_name, rt) :: env.aliases }
          ({ it = DType (b, rt); loc = d.loc } :: acc)
          rest
      | DLet bnd ->
        let cb, s = resolve_binding env bnd in
        let frames = F.letb (FBind (bnd.b_bind.bd_name, s)) env.frames in
        go { env with frames } ({ it = DLet cb; loc = d.loc } :: acc) rest
      | DModule (b, me) ->
        let cm, s = resolve_exp env me in
        let frames = F.letb (FBind (b.bd_name, s)) env.frames in
        go { env with frames } ({ it = DModule (b, cm); loc = d.loc } :: acc) rest
      | DOpen m ->
        let cm, sm = resolve_exp env m in
        let frames = F.openm (FFields (opened_fields m.loc sm)) env.frames in
        go { env with frames } ({ it = DOpen cm; loc = d.loc } :: acc) rest
      | DAdt _ -> err d.loc "internal: ADT declaration survived Adt.expand")
  in
  let decls, main = go empty_env [] p.decls in
  { imports = []; decls; main = Some main }
