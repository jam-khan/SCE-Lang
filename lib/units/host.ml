(* Host capabilities: `sys`, `str` and `loader` are leaf provider units the host
   materializes instead of loading. Their exports are Hostfn values dispatching
   through Eval.host_dispatch, so authority flows only through linking — a term
   never linked a capability cannot perform its effect, and `sandbox` cuts
   effects off with the rest of the context. *)

module S = Sce_core.Ast
module E = Sce_core.Elab
module C = Core_lambdae.Ast

open Artifact

(* Effects enter through a unit like any other dependency. `sys` is a
   host-implemented leaf provider, built next to the dispatcher below; its
   interface lives here so `import Sys` can fall back to it. *)

let sys_typ : S.typ =
  S.TAnd
    ( S.TRcd ("print", S.TArr (S.TString, S.TTop)),
      S.TRcd
        ( "readfile",
          S.TArr (S.TString, S.TOr (S.TString, S.TRcd ("err", S.TString))) ) )

(* Pure string introspection; strings are otherwise write-only (^ and =). *)
let str_typ : S.typ =
  S.TAnd
    ( S.TRcd ("head", S.TArr (S.TString, S.TString)),
      S.TRcd ("tail", S.TArr (S.TString, S.TString)) )

module Ev = Core_lambdae.Eval

(* Where `print` writes; tests redirect it to capture effect traces. *)
let out : (string -> unit) ref = ref print_string

let hostfn (name : string) (t : S.typ) : C.exp =
  match E.elab_typ t with
  | C.TArr (a, b) -> C.Hostfn (name, a, b)
  | _ -> err "internal: host capability %s is not a function" name

let host_artifact ~name ~label (t : S.typ) : t =
  let core =
    match
      List.map (fun (l, ft) -> C.Lrec (l, hostfn l ft)) (E.record_fields t)
    with
    | first :: rest -> List.fold_left (fun acc r -> C.Mrg (acc, r)) first rest
    | [] -> err "internal: host interface %s is not a record intersection" name
  in
  { a_name = name; a_imports = None;
    a_exports = S.TRcd (label, t); a_core = C.Lrec (label, core) }

let sys : t = host_artifact ~name:"sys" ~label:"Sys" sys_typ
let str : t = host_artifact ~name:"str" ~label:"Str" str_typ

(* The loader is a capability whose type *declares* what it expects:

     import Loader : { load : String -> (Sig | {err : String}) }

   The host reads that off the importing artifact and specializes to it. The
   runtime check is structural equality between Sig and the loaded artifact's
   slot type — the static linker's comparison, made later. The expected type
   rides in the Hostfn name as surface syntax, so a saved program
   re-manufactures its checker in a fresh process. *)

let loader_label = "Loader"

let loader_typ_of (t : S.typ) : S.typ =
  match t with
  | S.TRcd ("load", S.TArr (S.TString, S.TOr (want, S.TRcd ("err", S.TString))))
    -> want
  | _ ->
    err "the %s import must have type {load : String -> (Sig | {err : String})}"
      loader_label

let loader (arts : t list) : t =
  let declared =
    List.find_map
      (fun a ->
        match a.a_imports with
        | Some d -> List.assoc_opt loader_label (Linker.import_fields d)
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

let is_host_unit name = name = "sys" || name = "loader" || name = "str"

(* ---- the dispatcher ---- *)

let string_arg what v =
  match v with
  | C.Lit (C.String s) -> s
  | _ -> failwith ("Error: " ^ what ^ " expects a string")

let err_t = C.TRcd ("err", C.TString)

let do_load (want : S.typ) (path : string) : C.exp =
  let fail msg = C.Inr (E.elab_typ want, C.Lrec ("err", C.Lit (C.String msg))) in
  match load path with
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
        Some (fun v -> !out (string_arg "print" v ^ "\n"); C.Unit)
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
      | "head" ->
        Some
          (fun v ->
            let s = string_arg "head" v in
            C.Lit (C.String (if s = "" then "" else String.sub s 0 1)))
      | "tail" ->
        Some
          (fun v ->
            let s = string_arg "tail" v in
            C.Lit
              (C.String (if s = "" then "" else String.sub s 1 (String.length s - 1))))
      | _ when String.starts_with ~prefix:"load:" name ->
        let want =
          parse_typ ~what:"loader"
            (String.sub name 5 (String.length name - 5))
        in
        Some (fun v -> do_load want (string_arg "load" v))
      | _ -> None
