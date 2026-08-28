(* A compiled unit: a closed λE term plus the λSCE interface types it was
   compiled against, and the .scei format those types are written in. *)

module S = Sce_core.Ast
module C = Core_lambdae.Ast

exception Error of string

let err fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

type t = {
  a_name : string;          (* unit basename, for diagnostics and wasm linking *)
  a_imports : S.typ option; (* left-nested & of {M : T}; None for a leaf unit *)
  a_exports : S.typ;
  a_core : C.exp;           (* closed λE term *)
}

(* How a unit occupies a slot: a leaf by its exports, a functor by its
   signature. *)
let slot_typ (u : t) : S.typ =
  match u.a_imports with
  | None -> u.a_exports
  | Some d -> S.TSig (S.TyArrM (d, S.TyIntf u.a_exports))

(* Bump the trailing digits whenever the artifact shape or the ASTs change:
   Marshal gives no compatibility, so the magic is the only guard. *)
let magic = "SCEOBJ02"

let save (path : string) (a : t) : unit =
  let oc = open_out_bin path in
  output_string oc magic;
  Marshal.to_channel oc a [];
  close_out oc

let load (path : string) : t =
  let ic =
    try open_in_bin path
    with Sys_error m -> err "cannot open artifact: %s" m
  in
  let m = really_input_string ic (String.length magic) in
  if m <> magic then begin
    close_in ic;
    err "%s is not a compatible artifact (expected format %s)" path magic
  end;
  let a : t = Marshal.from_channel ic in
  close_in ic;
  a

(* Inverts the type grammar, so a generated .scei parses back to the same type.
   Levels mirror the parser: 0 typ (mu, =>) < 1 arrow < 2 union < 3 & < 4 atom.
   Mu binders are de Bruijn, so names are invented on the way out. *)

let mu_name k = if k < 26 then String.make 1 (Char.chr (97 + k)) else Printf.sprintf "t%d" k

let print_typ (t : S.typ) : string =
  let paren need s = if need then "(" ^ s ^ ")" else s in
  let rec pt env lvl = function
    | S.TInt -> "Int"
    | S.TBool -> "Bool"
    | S.TString -> "String"
    | S.TTop -> "Top"
    | S.TVar i -> (
      match List.nth_opt env i with
      | Some n -> n
      | None -> err "cannot print an open type (unbound mu variable)")
    | S.TRcd (l, a) -> "{" ^ l ^ " : " ^ pt env 0 a ^ "}"
    | S.TMu body ->
      let n = mu_name (List.length env) in
      paren (lvl > 0) ("mu " ^ n ^ ". " ^ pt (n :: env) 0 body)
    | S.TSig m -> paren (lvl > 0) (pm env m)
    | S.TArr (a, b) -> paren (lvl > 1) (pt env 2 a ^ " -> " ^ pt env 1 b)
    | S.TOr (a, b) -> paren (lvl > 2) (pt env 2 a ^ " | " ^ pt env 3 b)
    | S.TAnd (a, b) -> paren (lvl > 3) (pt env 3 a ^ " & " ^ pt env 4 b)
  and pm env = function
    | S.TyIntf t -> pt env 0 t
    | S.TyArrM (a, m) -> pt env 1 a ^ " => " ^ pm env m
  in
  pt [] 0 t

(* ---------------- .scei aliases ----------------

   An interface is aliases + a type, resolved before it meets the importing
   file's scope, so its aliases are substituted away at the named level: what
   `import` splices into the unit is a self-contained surface type. A mu of the
   same name shadows an alias inside its body.
*)

let rec subst_tname (name : string) (body : Ast.typ) (t : Ast.typ) : Ast.typ =
  let nd it : Ast.typ = { it; loc = t.loc } in
  let s = subst_tname name body in
  match t.it with
  | Ast.TVar a -> if String.equal a name then body else t
  | Ast.TInt | Ast.TBool | Ast.TString | Ast.TTop -> t
  | Ast.TArr (a, b) -> nd (Ast.TArr (s a, s b))
  | Ast.TAnd (a, b) -> nd (Ast.TAnd (s a, s b))
  | Ast.TOr (a, b) -> nd (Ast.TOr (s a, s b))
  | Ast.TSig (a, b) -> nd (Ast.TSig (s a, s b))
  | Ast.TRcd fs -> nd (Ast.TRcd (List.map (fun (l, ft) -> (l, s ft)) fs))
  | Ast.TMu (b, t') ->
    if String.equal b.Ast.bd_name name then t else nd (Ast.TMu (b, s t'))

let expand_aliases (i : Ast.intf) : Ast.typ =
  let subst t (n, body) = subst_tname n body t in
  (* each body is expanded against the earlier ones, so one pass suffices *)
  List.fold_left subst i.Ast.i_typ
    (List.fold_left
       (fun acc ((b : Ast.binder), tb) ->
         acc @ [ (b.Ast.bd_name, List.fold_left subst tb acc) ])
       [] i.Ast.i_aliases)

(* Parse a type in surface syntax back to S.typ (aliases allowed first). *)
let parse_typ_exn ~what (src : string) : S.typ =
  match Driver.parse_intf src with
  | Error e -> err "%s:%d:%d: %s" what e.line e.col e.message
  | Ok intf -> Sugar.conv_typ_closed (expand_aliases intf)

(* Parse a type in surface syntax back to S.typ (aliases allowed first). *)
let parse_typ ~what (src : string) : S.typ =
  match Driver.parse_intf src with
  | Error e -> err "%s:%d:%d: %s" what e.line e.col e.message
  | Ok intf -> Sugar.conv_typ_closed (expand_aliases intf)
