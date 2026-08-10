(* Separate compilation: units, interfaces, and the core-level linker.

   A unit is a *sandboxed functor* from its imports to its exports — closed by
   the calculus itself (`sandbox` elaborates under Top), not by toolchain
   discipline. Its compiled form is an ordinary closed λE term stored in an
   artifact together with its λSCE-level interface types.

   Linking is the calculus's own first-class linking: each step applies the
   unit functor to a record of projections wired out of the accumulated
   provider — built with `Elab.wire_arg`, the very code `Mlink` elaboration
   uses — and merges the result in. The linked program is an ordinary λE term,
   re-checked by the ordinary λE typechecker. *)

module S = Sce_core.Ast
module E = Sce_core.Elab
module C = Core_lambdae.Ast

exception Error of string

let err fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

(* ---------------- artifacts ---------------- *)

type artifact = {
  a_name : string;          (* unit basename, for diagnostics and wasm linking *)
  a_imports : S.typ option; (* left-nested & of {M : T}; None for a leaf unit *)
  a_exports : S.typ;
  a_core : C.exp;           (* closed λE term *)
}

(* Bump the trailing digits whenever the artifact shape or the ASTs change:
   Marshal gives no compatibility, so the magic is the only guard. *)
let magic = "SCEOBJ01"

let save_artifact (path : string) (a : artifact) : unit =
  let oc = open_out_bin path in
  output_string oc magic;
  Marshal.to_channel oc a [];
  close_out oc

let load_artifact (path : string) : artifact =
  let ic =
    try open_in_bin path
    with Sys_error m -> err "cannot open artifact: %s" m
  in
  let m = really_input_string ic (String.length magic) in
  if m <> magic then begin
    close_in ic;
    err "%s is not a compatible artifact (expected format %s)" path magic
  end;
  let a : artifact = Marshal.from_channel ic in
  close_in ic;
  a

(* ---------------- surface-type printer ----------------

   Inverts the type grammar, so generated .scei files parse back to the same
   λSCE type. Levels mirror the parser: 0 typ (mu, =>) < 1 arrow < 2 union <
   3 intersection < 4 atom. Mu binders are de Bruijn in S.typ, so names are
   invented on the way out. *)

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

(* Parse a type in surface syntax back to S.typ (aliases allowed first). *)
let parse_typ_exn ~what (src : string) : S.typ =
  match Driver.parse_intf src with
  | Error e -> err "%s:%d:%d: %s" what e.line e.col e.message
  | Ok intf ->
    let named = Debruijn.expand_aliases intf.i_aliases intf.i_typ in
    Sugar.conv_typ (Debruijn.resolve_typ Debruijn.empty_env named)

(* ---------------- imports and the unit wrapper ---------------- *)

(* Resolve one import header to a self-contained *named* type, so it can be
   spliced into the unit file before scope resolution. File-based interfaces
   live next to the importing source file. *)
let import_typ ~dir (b : Ast.binder) (src : string Ast.import_source) :
    string Ast.typ =
  let from_file base =
    let path = Filename.concat dir (base ^ ".scei") in
    let content =
      try
        let ic = open_in_bin path in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      with Sys_error _ ->
        err "import %s: interface file %s not found" b.bd_name path
    in
    match Driver.parse_intf content with
    | Error e -> err "%s:%d:%d: %s" path e.line e.col e.message
    | Ok intf -> Debruijn.expand_aliases intf.i_aliases intf.i_typ
  in
  match src with
  | Ast.IAuto -> from_file b.bd_name
  | Ast.IFile base -> from_file base
  | Ast.IInline t -> t

let imports_binder = "%imports"

(* The whole design in one function: a unit is its declarations wrapped as a
   sandboxed struct, or — when it imports — a sandboxed functor whose
   parameter is the record of imports, opened over the body. Everything
   downstream (Debruijn, Sugar, Elab) is the unchanged whole-program
   machinery. *)
let unit_wrapper (imports : (Ast.binder * string Ast.typ) list)
    (p : Ast.named) : Ast.named =
  let loc = Ast.dummy_loc in
  let node it : (string, string) Ast.exp = { it; loc } in
  let wrapped =
    match imports with
    | [] -> node (Ast.EStruct (Ast.Sandboxed, p.decls))
    | _ ->
      let fields = List.map (fun (b, t) -> (b.Ast.bd_name, t)) imports in
      let param =
        {
          Ast.p_bind = { Ast.bd_name = imports_binder; bd_loc = loc };
          p_typ = { Ast.it = Ast.TRcd fields; loc };
        }
      in
      node
        (Ast.EFunctor
           ( Ast.Sandboxed,
             [ param ],
             node
               (Ast.EOpen
                  ( node (Ast.EVar imports_binder),
                    node (Ast.EStruct (Ast.Open, p.decls)) )) ))
  in
  { Ast.imports = []; decls = []; main = Some wrapped }

(* Split the synthesized unit type into interface halves. *)
let unit_info (t : S.typ) : S.typ option * S.typ =
  match t with
  | S.TSig (S.TyArrM (i, S.TyIntf e)) -> (Some i, e)
  | t -> (None, t)

(* ---------------- the linker ---------------- *)

let rec import_fields = function
  | S.TRcd (l, t) -> [ (l, t) ]
  | S.TAnd (a, b) -> import_fields a @ import_fields b
  | t -> err "malformed import interface: %s" (print_typ t)

let rec export_labels = function
  | S.TRcd (l, _) -> [ l ]
  | S.TAnd (a, b) -> export_labels a @ export_labels b
  | _ -> []

(* Would merging `next` into a provider typed `accT` make any label ambiguous?
   `srlookup` refuses a label present on both sides, so a collision would make
   both copies unreachable — reject it with the unit names attached. *)
let check_no_overlap accT acc_names next next_name =
  List.iter
    (fun l ->
      if E.label_in l accT then
        err "units %s and %s both export '%s'; the label would become ambiguous"
          (String.concat "+" acc_names) next_name l)
    (export_labels next)

let check_imports_satisfied ~unit_name accT d =
  List.iter
    (fun (l, want) ->
      match E.srlookup_opt accT l with
      | Some got when got = want -> ()
      | Some got ->
        err
          "unit %s imports %s : %s but the linked providers export %s : %s \
           (stale .scei?)"
          unit_name l (print_typ want) l (print_typ got)
      | None ->
        err "unit %s imports '%s', which no linked provider exports \
             unambiguously" unit_name l)
    (import_fields d)

(* One link step as a λE term implementing the calculus's linking principle:
   apply the unit functor to a record of projections wired out of the
   provider, and merge the result in.

     step = λ(acc : accT). λ(u : d -> b). Mrg (?.1, u (wire d))
     wire {l : A}      = Lrec (l, Rproj (?.1, l))
     wire (d1 & d2)    = Mrg (wire d1, wire d2)

   The provider is bound *once* as ?.1 and every import label projects from
   that binding. This deliberately does not reuse `Elab.linked_core_n`: its
   sharing wrapper reaches for fixed slots of the ambient environment
   (`?.0`/`?.1` of a self-application), which is only right at the
   whole-program elaboration sites it was written for. Binding the provider
   explicitly is insensitive to where the step is spliced — and the λE
   typechecker verifies it on every link. *)
let link_step (accT : S.typ) (d : S.typ) (b : S.typ) : C.exp =
  let accT_c = E.elab_typ accT in
  let tu_c = E.elab_typ (S.TSig (S.TyArrM (d, S.TyIntf b))) in
  (* λE's Mrg is dependent: its right operand is checked and evaluated under
     the context extended with the left value. So inside the outer Mrg the
     provider is slot 0 (freshly merged) and the functor slot 1 — and every
     nested merge inside the wire record shifts the provider one further. *)
  let rec wire shift = function
    | S.TRcd (l, _) -> C.Lrec (l, C.Rproj (C.Proj (C.Query, shift), l))
    | S.TAnd (d1, d2) -> C.Mrg (wire shift d1, wire (shift + 1) d2)
    | t -> err "malformed import interface: %s" (print_typ t)
  in
  C.Lam
    ( accT_c,
      C.Lam
        ( tu_c,
          C.Mrg
            ( C.Proj (C.Query, 1),
              C.App (C.Proj (C.Query, 1), wire 0 d) ) ) )

let link (arts : artifact list) : artifact =
  match arts with
  | [] -> err "nothing to link"
  | first :: rest ->
    (match first.a_imports with
     | Some _ ->
       err "the first unit (%s) has imports; linking is left to right, so it \
            must be a leaf" first.a_name
     | None -> ());
    let acc =
      List.fold_left
        (fun (accT, acc, names) u ->
          check_no_overlap accT names u.a_exports u.a_name;
          match u.a_imports with
          | None ->
            (S.TAnd (accT, u.a_exports), C.Mrg (acc, u.a_core),
             names @ [ u.a_name ])
          | Some d ->
            check_imports_satisfied ~unit_name:u.a_name accT d;
            let step = link_step accT d u.a_exports in
            ( S.TAnd (accT, u.a_exports),
              C.App (C.App (step, acc), u.a_core),
              names @ [ u.a_name ] ))
        (first.a_exports, first.a_core, [ first.a_name ])
        rest
    in
    let accT, core, names = acc in
    (* The linker is only right if its output is well-typed λE. *)
    (try ignore (Core_lambdae.Check.typecheck core)
     with Core_lambdae.Check.Type_error m ->
       err "internal: linked program failed to typecheck: %s" m);
    { a_name = String.concat "+" names; a_imports = None;
      a_exports = accT; a_core = core }

(* ---------------- running a linked artifact ----------------

   Convention: a `main` export is the program; otherwise the module itself is
   the result. *)

let runnable (a : artifact) : S.typ * C.exp =
  match E.srlookup_opt a.a_exports "main" with
  | Some t -> (t, C.Rproj (a.a_core, "main"))
  | None -> (a.a_exports, a.a_core)
