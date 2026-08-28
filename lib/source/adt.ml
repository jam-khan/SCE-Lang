(* ADT sugar: named AST -> named AST. `type t = | C of T * T | D` becomes a
   plain alias over left-nested unions, records for tuple payloads, Top for
   nullary ones, and `mu t. ...` when a payload mentions t; uses and `match`
   become the ascribed inl/inr/fold/case idioms a user could write by hand.
   Constructors scope like type aliases; value binders shadow them. *)

open Ast

exception Error of string * loc

let err loc fmt = Printf.ksprintf (fun s -> raise (Error (s, loc))) fmt

type info = {
  a_name : string;
  a_rec : bool;
  a_ctors : (string * int) array;  (* name, payload count, declaration order *)
  a_sums : typ array;       (* a_sums.(k) = payloads 0..k, left-nested | *)
}

type item = Ctor of int * info | Shadow

type env = (string * item) list

let lookup env c =
  match List.assoc_opt c env with Some (Ctor (i, ad)) -> Some (i, ad) | _ -> None

let shadow env names =
  List.fold_left (fun env (b : binder) -> (b.bd_name, Shadow) :: env) env names

let shadow_params env ps = shadow env (List.map (fun p -> p.p_bind) ps)

(* A redeclared type name orphans the constructors of its predecessor. *)
let drop_adt env name =
  List.filter (function _, Ctor (_, ad) -> ad.a_name <> name | _ -> true) env

let rec mentions name (t : typ) =
  match t.it with
  | TVar a -> String.equal a name
  | TInt | TBool | TString | TTop -> false
  | TArr (a, b) | TAnd (a, b) | TOr (a, b) | TSig (a, b) ->
    mentions name a || mentions name b
  | TRcd fs -> List.exists (fun (_, ft) -> mentions name ft) fs
  | TMu (b, body) -> (not (String.equal b.bd_name name)) && mentions name body

(* How a constructor must be written, for every arity error. *)
let payload_hint c = function
  | 0 -> "carries no payload"
  | 1 -> Printf.sprintf "carries one payload, as in `%s x`" c
  | k ->
    Printf.sprintf "carries %d payloads, as in `%s (%s)`" k c
      (String.concat ", " (List.init k (fun j -> "x" ^ string_of_int (j + 1))))

let payload_typ loc = function
  | [] -> mk loc TTop
  | [ t ] -> t
  | ts -> mk loc (TRcd (List.mapi (fun i t -> ("_" ^ string_of_int (i + 1), t)) ts))

let counter = ref 0

let fresh prefix loc =
  incr counter;
  { bd_name = Printf.sprintf "%%%s%d" prefix !counter; bd_loc = loc }

(* ---------------- declarations of ADTs ---------------- *)

let process_adt env (b : binder) ctors =
  let rec dups seen = function
    | [] -> ()
    | ((cb : binder), _) :: rest ->
      if String.equal cb.bd_name "_" then
        err cb.bd_loc "'_' cannot be a constructor name";
      if List.mem cb.bd_name seen then
        err cb.bd_loc "duplicate constructor `%s` in type `%s`" cb.bd_name
          b.bd_name
      else dups (cb.bd_name :: seen) rest
  in
  dups [] ctors;
  let n = List.length ctors in
  let payloads =
    Array.of_list (List.map (fun ((cb : binder), ts) -> payload_typ cb.bd_loc ts) ctors)
  in
  let sums = Array.make n payloads.(0) in
  for k = 1 to n - 1 do
    sums.(k) <- mk b.bd_loc (TOr (sums.(k - 1), payloads.(k)))
  done;
  let recursive = mentions b.bd_name sums.(n - 1) in
  let alias =
    if recursive then mk b.bd_loc (TMu (b, sums.(n - 1))) else sums.(n - 1)
  in
  let ad =
    { a_name = b.bd_name;
      a_rec = recursive;
      a_ctors =
        Array.of_list
          (List.map (fun ((cb : binder), ts) -> (cb.bd_name, List.length ts)) ctors);
      a_sums = sums }
  in
  let env = drop_adt env b.bd_name in
  let env =
    List.fold_left
      (fun (env, i) ((cb : binder), _) -> ((cb.bd_name, Ctor (i, ad)) :: env, i + 1))
      (env, 0) ctors
    |> fst
  in
  (alias, env)

(* ---------------- constructing ---------------- *)

(* The value for constructor i in the left-nested sum: constructor k is `inr`
   at level k, everything below wraps in `inl`, and every injection except
   the innermost carries the sum type of its level (sugar checks each). *)
let inject loc (ad : info) i v =
  let n = Array.length ad.a_ctors in
  if n = 1 then v
  else
    let rec at k =
      if k = 0 then v
      else if i = k then mk loc (EInr v)
      else
        let inner = at (k - 1) in
        let inner =
          if k = 1 then inner else mk loc (EAnnot (inner, ad.a_sums.(k - 1)))
        in
        mk loc (EInl inner)
    in
    at (n - 1)

let construct loc (ad : info) i (arg : exp option) =
  let cname, arity = ad.a_ctors.(i) in
  let v =
    match (arity, arg) with
    | 0, None -> mk loc EUnit
    | 0, Some _ -> err loc "constructor `%s` takes no argument" cname
    | _, Some a -> a
    | k, None -> err loc "constructor `%s` %s" cname (payload_hint cname k)
  in
  let n = Array.length ad.a_ctors in
  let self = mk loc (TVar ad.a_name) in
  let body = inject loc ad i v in
  if ad.a_rec then
    let body =
      if n = 1 then body else mk loc (EAnnot (body, ad.a_sums.(n - 1)))
    in
    mk loc (EAnnot (mk loc (EFold body), self))
  else mk loc (EAnnot (body, self))

(* ---------------- expressions ---------------- *)

let is_ctor env = function
  | { it = EVar c; _ } -> Option.is_some (lookup env c)
  | _ -> false

let rec walk env (e : exp) : exp =
  let nd it = { it; loc = e.loc } in
  match e.it with
  | EVar c -> (
    match lookup env c with
    | Some (i, ad) -> construct e.loc ad i None
    | None -> e)
  | EApp (f, a) when is_ctor env f -> (
    match f.it with
    | EVar c ->
      let i, ad = Option.get (lookup env c) in
      construct e.loc ad i (Some (walk env a))
    | _ -> assert false)
  | EApp (({ it = EApp (f', _); _ } as f), a) when is_ctor env f' ->
    (match f'.it with
     | EVar c ->
       err e.loc
         "constructor `%s` takes a single argument; a tuple payload is one \
          argument, as in `%s (x, y)`" c c
     | _ -> ignore (walk env f); ignore (walk env a); assert false)
  | EMatch (scrut, arms) -> rewrite_match env e.loc scrut arms
  | ELit _ | EUnit | EQuery -> e
  | EAnnot (e1, t) -> nd (EAnnot (walk env e1, t))
  | EBinop (op, a, b) -> nd (EBinop (op, walk env a, walk env b))
  | EUnop (op, a) -> nd (EUnop (op, walk env a))
  | EIf (c, t, f) -> nd (EIf (walk env c, walk env t, walk env f))
  | ELam (ps, body) -> nd (ELam (ps, walk (shadow_params env ps) body))
  | EApp (f, a) -> nd (EApp (walk env f, walk env a))
  | ERcd fs -> nd (ERcd (List.map (fun (l, fe) -> (l, walk env fe)) fs))
  | EField (b, l) -> nd (EField (walk env b, l))
  | EIndex (b, n) -> nd (EIndex (walk env b, n))
  | EMerge (k, a, b) -> nd (EMerge (k, walk env a, walk env b))
  | ELet (b, body) ->
    nd (ELet (walk_binding env b, walk (shadow env [ b.b_bind ]) body))
  | EOpen (m, body) -> nd (EOpen (walk env m, walk env body))
  | EBox (m, body) -> nd (EBox (walk env m, walk env body))
  | EInl a -> nd (EInl (walk env a))
  | EInr a -> nd (EInr (walk env a))
  | EFold a -> nd (EFold (walk env a))
  | EUnfold a -> nd (EUnfold (walk env a))
  | ECase (scrut, x, e1, y, e2) ->
    nd
      (ECase
         ( walk env scrut,
           x, walk (shadow env [ x ]) e1,
           y, walk (shadow env [ y ]) e2 ))
  | EStruct (sb, ds) ->
    let ds, _ = walk_decls env ds in
    nd (EStruct (sb, ds))
  | EFunctor (sb, ps, body) ->
    nd (EFunctor (sb, ps, walk (shadow_params env ps) body))
  | ELink (k, m, f) -> nd (ELink (k, walk env m, walk env f))

and walk_binding env (b : binding) =
  let inner = shadow_params env b.b_params in
  let inner = if b.b_rec then shadow inner [ b.b_bind ] else inner in
  { b with b_exp = walk inner b.b_exp }

(* ---------------- match ---------------- *)

and rewrite_match env loc scrut arms =
  let cscrut = walk env scrut in
  let ad =
    match
      List.find_opt (fun ((c : binder), _, _) -> c.bd_name <> "_") arms
    with
    | None ->
      err loc "`match` needs at least one constructor arm; only `_` was given"
    | Some (c, _, _) -> (
      match lookup env c.bd_name with
      | Some (_, ad) -> ad
      | None -> err c.bd_loc "unknown constructor `%s`" c.bd_name)
  in
  let n = Array.length ad.a_ctors in
  (* one slot per constructor, filled from the arms in any order *)
  let slots = Array.make n None in
  let wild = ref None in
  List.iteri
    (fun k ((c : binder), args, body) ->
      if c.bd_name = "_" then begin
        if args <> [] then err c.bd_loc "the `_` arm binds nothing";
        if !wild <> None then err c.bd_loc "duplicate `_` arm";
        if k <> List.length arms - 1 then
          err c.bd_loc "the `_` arm must come last";
        wild := Some body
      end
      else
        match lookup env c.bd_name with
        | None -> err c.bd_loc "unknown constructor `%s`" c.bd_name
        | Some (_, ad') when ad' != ad ->
          err c.bd_loc "`%s` belongs to type `%s`, not `%s`" c.bd_name
            ad'.a_name ad.a_name
        | Some (i, _) ->
          if slots.(i) <> None then
            err c.bd_loc "duplicate arm for constructor `%s`" c.bd_name;
          slots.(i) <- Some (c, args, body))
    arms;
  (* each slot becomes a case binder and a walked body *)
  let branch i =
    let cname, arity = ad.a_ctors.(i) in
    match slots.(i) with
    | None -> (
      match !wild with
      | Some body -> (fresh "w" loc, walk env body)
      | None ->
        err loc "`match` does not cover constructor `%s` of type `%s`" cname
          ad.a_name)
    | Some (c, args, body) -> (
      match (arity, args) with
      | 0, [] -> (fresh "w" c.bd_loc, walk env body)
      (* one binder takes the whole payload, tuple or not *)
      | k, [ x ] when k >= 1 -> (x, walk (shadow env [ x ]) body)
      (* C (x, y): bind the payload record, then a let per field *)
      | k, xs when k > 1 && List.length xs = k ->
        let p = fresh "p" c.bd_loc in
        let field j (x : binder) acc =
          let proj =
            mk x.bd_loc
              (EField (mk x.bd_loc (EVar p.bd_name), "_" ^ string_of_int (j + 1)))
          in
          mk x.bd_loc
            (ELet
               ( { b_rec = false; b_bind = x; b_params = []; b_ann = None;
                   b_exp = proj },
                 acc ))
        in
        ( p,
          List.fold_right (fun (j, x) -> field j x)
            (List.mapi (fun j x -> (j, x)) xs)
            (walk (shadow env xs) body) )
      | k, _ -> err c.bd_loc "constructor `%s` %s" cname (payload_hint cname k))
  in
  if !wild <> None && Array.for_all (fun s -> s <> None) slots then
    err loc "the `_` arm is unreachable: every constructor of `%s` is covered"
      ad.a_name;
  let self = mk scrut.loc (TVar ad.a_name) in
  let annotated = mk scrut.loc (EAnnot (cscrut, self)) in
  let scrut' =
    if ad.a_rec then mk scrut.loc (EUnfold annotated) else annotated
  in
  if n = 1 then
    let b, body = branch 0 in
    mk loc
      (ELet
         ( { b_rec = false; b_bind = b; b_params = []; b_ann = None;
             b_exp = scrut' },
           body ))
  else
    (* mirror of `inject`: constructor k is the inr branch at level k *)
    let rec tree k scrut_e =
      if k = 1 then
        let b0, e0 = branch 0 and b1, e1 = branch 1 in
        mk loc (ECase (scrut_e, b0, e0, b1, e1))
      else
        let bk, ek = branch k in
        let m = fresh "m" loc in
        mk loc
          (ECase (scrut_e, m, tree (k - 1) (mk loc (EVar m.bd_name)), bk, ek))
    in
    tree (n - 1) scrut'

(* ---------------- declarations and programs ---------------- *)

and walk_decls env (ds : decl list) :
    decl list * env =
  let step (acc, env) (d : decl) =
    match d.it with
    | DAdt (b, ctors) ->
      let alias, env = process_adt env b ctors in
      ({ it = DType (b, alias); loc = d.loc } :: acc, env)
    | DType (b, _) -> (d :: acc, drop_adt env b.bd_name)
    | DLet b ->
      ({ it = DLet (walk_binding env b); loc = d.loc } :: acc,
        shadow env [ b.b_bind ])
    | DModule (b, e) ->
      ({ it = DModule (b, walk env e); loc = d.loc } :: acc, shadow env [ b ])
    | DOpen e -> ({ it = DOpen (walk env e); loc = d.loc } :: acc, env)
  in
  let acc, env = List.fold_left step ([], env) ds in
  (List.rev acc, env)

let expand (p : Ast.program) : Ast.program =
  counter := 0;
  let decls, env = walk_decls [] p.decls in
  { p with decls; main = Option.map (walk env) p.main }