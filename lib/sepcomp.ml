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
let magic = "SCEOBJ02"

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

(* ---------------- the sys interface ----------------

   Effects enter the language the same way every other dependency does:
   through a unit. `sys` is a host-implemented leaf provider (built further
   down, next to the dispatcher); its interface lives here so `import Sys`
   can fall back to it when no Sys.scei file shadows the builtin. *)

let sys_typ : S.typ =
  S.TAnd
    ( S.TRcd ("print", S.TArr (S.TString, S.TTop)),
      S.TRcd
        ( "readfile",
          S.TArr (S.TString, S.TOr (S.TString, S.TRcd ("err", S.TString))) ) )

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
        (* `import Sys` falls back to the built-in host interface, unless a
           Sys.scei file shadows it. *)
        if base = "Sys" then print_typ sys_typ
        else err "import %s: interface file %s not found" b.bd_name path
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

(* One link step: apply the unit functor to a record of projections wired out
   of the provider, and merge the result in. This is `Elab.link_step` — the
   very term `link`/`linkall` elaborate to — so the two linkers cannot drift:
   both bind each operand exactly once, and the λE typechecker verifies the
   result on every link. *)
let link_step (accT : S.typ) (d : S.typ) (b : S.typ) : C.exp =
  E.link_step (E.elab_typ accT)
    (E.elab_typ (S.TSig (S.TyArrM (d, S.TyIntf b))))
    d

(* A leaf step is a non-dependent merge of the unit into the provider. *)
let link_step_leaf (accT : S.typ) (uT : S.typ) : C.exp =
  E.nmrg_step (E.elab_typ accT) (E.elab_typ uT)

(* How a unit occupies a slot: a leaf by its exports, a functor by its
   signature. *)
let slot_typ (u : artifact) : S.typ =
  match u.a_imports with
  | None -> u.a_exports
  | Some d -> S.TSig (S.TyArrM (d, S.TyIntf u.a_exports))

(* The composition both linkers share: a left fold of step applications,
   `App (App (step_k, acc), u_k)`, parameterized by how a unit occurrence is
   spelled — the core linker splices the closed artifact terms in, the wasm
   linker references the units through the environment its link module builds
   from imports. Same term, two ways of installing the units. *)
let compose (arts : artifact list) (uref : int -> C.exp) :
    S.typ * C.exp * string list =
  match arts with
  | [] -> err "nothing to link"
  | first :: rest ->
    (match first.a_imports with
     | Some _ ->
       err "the first unit (%s) has imports; linking is left to right, so it \
            must be a leaf" first.a_name
     | None -> ());
    let accT, core, names, _ =
      List.fold_left
        (fun (accT, acc, names, k) u ->
          check_no_overlap accT names u.a_exports u.a_name;
          let step =
            match u.a_imports with
            | None -> link_step_leaf accT u.a_exports
            | Some d ->
              check_imports_satisfied ~unit_name:u.a_name accT d;
              link_step accT d u.a_exports
          in
          ( S.TAnd (accT, u.a_exports),
            C.App (C.App (step, acc), uref k),
            names @ [ u.a_name ],
            k + 1 ))
        (first.a_exports, uref 0, [ first.a_name ], 1)
        rest
    in
    (accT, core, names)

let link (arts : artifact list) : artifact =
  let accT, core, names =
    compose arts (fun k -> (List.nth arts k).a_core)
  in
  (* The linker is only right if its output is well-typed λE. *)
  (try ignore (Core_lambdae.Check.typecheck core)
   with Core_lambdae.Check.Type_error m ->
     err "internal: linked program failed to typecheck: %s" m);
  { a_name = String.concat "+" names; a_imports = None;
    a_exports = accT; a_core = core }

(* The wasm linker's half of the bargain: the same composition, with unit k
   referenced as `?.(n-1-k)` — the link module's main builds its environment
   by merging the imported unit values, so `Query` *is* the loaded units. *)
let wasm_link_parts (arts : artifact list) :
    string list * Core_lambdae.Ast.typ list * C.exp =
  let n = List.length arts in
  let accT, body, names =
    compose arts (fun k -> C.Proj (C.Query, n - 1 - k))
  in
  let body =
    match E.srlookup_opt accT "main" with
    | Some _ -> C.Rproj (body, "main")
    | None -> body
  in
  (names, List.map (fun a -> E.elab_typ (slot_typ a)) arts, body)

(* ---------------- running a linked artifact ----------------

   Convention: a `main` export is the program; otherwise the module itself is
   the result. *)

let runnable (a : artifact) : S.typ * C.exp =
  (match a.a_imports with
   | Some d ->
     err "unit %s still imports %s; link it against its providers first"
       a.a_name
       (String.concat ", " (List.map fst (import_fields d)))
   | None -> ());
  match E.srlookup_opt a.a_exports "main" with
  | Some t -> (t, C.Rproj (a.a_core, "main"))
  | None -> (a.a_exports, a.a_core)

(* ---------------- host capabilities ----------------

   `sys` and `loader` are leaf provider units the *host* materializes rather
   than loads from disk. Their exports are Hostfn values dispatching into
   OCaml through Eval.host_dispatch, so authority flows only through linking:
   a term that was never linked (or handed) a capability cannot perform its
   effect, and `sandbox` cuts effects off with the rest of the context. *)

module Ev = Core_lambdae.Eval

(* Where `print` writes; tests redirect it to capture effect traces. *)
let host_out : (string -> unit) ref = ref print_string

let hostfn (name : string) (t : S.typ) : C.exp =
  match E.elab_typ t with
  | C.TArr (a, b) -> C.Hostfn (name, a, b)
  | _ -> err "internal: host capability %s is not a function" name

let sys_artifact : artifact =
  let field l t = (l, hostfn l t) in
  let fields =
    match sys_typ with
    | S.TAnd (S.TRcd (l1, t1), S.TRcd (l2, t2)) -> [ field l1 t1; field l2 t2 ]
    | _ -> err "internal: sys_typ is not a two-field record intersection"
  in
  let core =
    match List.map (fun (l, e) -> C.Lrec (l, e)) fields with
    | first :: rest -> List.fold_left (fun acc r -> C.Mrg (acc, r)) first rest
    | [] -> assert false
  in
  { a_name = "sys"; a_imports = None;
    a_exports = S.TRcd ("Sys", sys_typ); a_core = C.Lrec ("Sys", core) }

(* The loader is a capability whose type *declares* the expected interface:

     import Loader : { load : String -> (Sig | {err : String}) }

   The host reads that declaration off the importing artifact and builds a
   provider specialized to it. The runtime check is structural equality
   between Sig and the loaded artifact's slot type — the same comparison the
   static linker makes, at a later time. The expected type rides in the
   Hostfn name as printed surface syntax, which parses back to an equal type
   (print_typ inverts the grammar), so a saved linked program re-manufactures
   its checker in a fresh process. *)

let loader_label = "Loader"

let loader_typ_of (t : S.typ) : S.typ =
  match t with
  | S.TRcd ("load", S.TArr (S.TString, S.TOr (want, S.TRcd ("err", S.TString))))
    -> want
  | _ ->
    err "the %s import must have type {load : String -> (Sig | {err : String})}"
      loader_label

let loader_artifact (arts : artifact list) : artifact =
  let declared =
    List.find_map
      (fun a ->
        match a.a_imports with
        | Some d -> List.assoc_opt loader_label (import_fields d)
        | None -> None)
      arts
  in
  match declared with
  | None ->
    err "no unit imports %s, so there is no loader interface to satisfy"
      loader_label
  | Some t ->
    let want = loader_typ_of t in
    { a_name = "loader"; a_imports = None;
      a_exports = S.TRcd (loader_label, t);
      a_core =
        C.Lrec (loader_label,
          C.Lrec ("load",
            hostfn ("load:" ^ print_typ want)
              (S.TArr (S.TString, S.TOr (want, S.TRcd ("err", S.TString)))))) }

let is_host_unit name = name = "sys" || name = "loader"

(* ---- the dispatcher ---- *)

let string_arg what v =
  match v with
  | C.Lit (C.String s) -> s
  | _ -> failwith ("Error: " ^ what ^ " expects a string")

let err_t = C.TRcd ("err", C.TString)

let do_load (want : S.typ) (path : string) : C.exp =
  let fail msg = C.Inr (E.elab_typ want, C.Lrec ("err", C.Lit (C.String msg))) in
  match load_artifact path with
  | exception Error m -> fail m
  | a ->
    if slot_typ a = want then C.Inl (err_t, Ev.eval C.Unit a.a_core)
    else
      fail
        (Printf.sprintf "%s : %s does not match the expected %s" path
           (print_typ (slot_typ a)) (print_typ want))

let () =
  Ev.host_dispatch :=
    fun name ->
      match name with
      | "print" ->
        Some (fun v -> !host_out (string_arg "print" v ^ "\n"); C.Unit)
      | "readfile" ->
        Some
          (fun v ->
            let path = string_arg "readfile" v in
            try
              let ic = open_in_bin path in
              let s = really_input_string ic (in_channel_length ic) in
              close_in ic;
              C.Inl (err_t, C.Lit (C.String s))
            with Sys_error m -> C.Inr (C.TString, C.Lrec ("err", C.Lit (C.String m))))
      | _ when String.starts_with ~prefix:"load:" name ->
        let want =
          parse_typ_exn ~what:"loader"
            (String.sub name 5 (String.length name - 5))
        in
        Some (fun v -> do_load want (string_arg "load" v))
      | _ -> None
