(* The core-level linker: each step applies a unit functor to projections wired
   out of the accumulated provider with `Elab.link_step` — the very term `Mlink`
   elaborates to — and merges the result in, re-checked as ordinary λE. *)

module S = Sce_core.Ast
module E = Sce_core.Elab
module C = Core_lambdae.Ast

open Artifact

let import_fields t =
  match E.record_fields t with
  | [] -> err "malformed import interface: %s" (print_typ t)
  | fs -> fs

let export_labels t = List.map fst (E.record_fields t)

(* A label on both sides is unreachable through `srlookup`, so a collision
   between units is an error, not a shadowing. *)
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

(* One link step is Elab's own `linked_core` — the term `link`/`linkall`
   elaborate to — so the toolchain linker and the calculus's cannot drift; a
   leaf unit joins by `nmrg_core`. Neither captures anything from its operands'
   scope, which is what lets the wasm linker apply them to units it only reaches
   through its environment. *)
let step (accT : S.typ) (u : t) (acc : C.exp) (ue : C.exp) : C.exp =
  match u.a_imports with
  | None -> E.nmrg_core acc ue
  | Some d ->
    check_imports_satisfied ~unit_name:u.a_name accT d;
    E.linked_core (E.elab_typ accT) (E.elab_typ d) (E.elab_typ u.a_exports) acc ue

(* The composition both linkers share: a left fold of `step`, parameterized by
   how a unit occurrence is spelled — spliced term for the core linker,
   environment projection for the wasm one. *)
let compose (arts : t list) (uref : int -> C.exp) :
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
          ( S.TAnd (accT, u.a_exports),
            step accT u acc (uref k),
            names @ [ u.a_name ],
            k + 1 ))
        (first.a_exports, uref 0, [ first.a_name ], 1)
        rest
    in
    (accT, core, names)

let link (arts : t list) : t =
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
let wasm_parts (arts : t list) :
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

(* A `main` export is the program; otherwise the module itself is the result. *)

let runnable (a : t) : S.typ * C.exp =
  (match a.a_imports with
   | Some d ->
     err "unit %s still imports %s; link it against its providers first"
       a.a_name
       (String.concat ", " (List.map fst (import_fields d)))
   | None -> ());
  match E.srlookup_opt a.a_exports "main" with
  | Some t -> (t, C.Rproj (a.a_core, "main"))
  | None -> (a.a_exports, a.a_core)

