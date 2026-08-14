(* The whole front-to-back pipeline:

     parse -> resolve -> desugar -> elaborate -> check -> evaluate

   Every stage reports failures the same way, so a caller only ever has to
   render one kind of error. *)

module C = Core_lambdae.Ast
module S = Sce_core.Ast

type error = {
  stage : string;
  message : string;
  line : int; (* 1-based *)
  col : int;  (* 0-based *)
}

type outcome = {
  sce_typ : S.typ;      (* the type synthesized while desugaring *)
  sce_exp : S.exp;      (* the λSCE term *)
  core_typ : C.typ;     (* the type λE independently assigns to the elaboration *)
  core_exp : C.exp;     (* the elaborated λE term *)
  value : C.exp;        (* the result of evaluating it *)
}

let at stage (loc : Ast.loc) message =
  let line, col = Driver.line_col loc.start_p in
  { stage; message; line; col }

(* Stages after parsing have no position of their own to report; they inherit
   the one carried by the surface node that raised. *)
let whole stage message = { stage; message; line = 1; col = 0 }

(* The interpreters raise Failure with their own "Error: " prefix. *)
let strip_error_prefix m =
  let p = "Error: " in
  if String.starts_with ~prefix:p m then
    String.sub m (String.length p) (String.length m - String.length p)
  else m

(* Parse, then run `k` with every later stage's exception mapped to `error`. *)
let staged (src : string) (k : Ast.named -> 'a) : ('a, error) result =
  match Driver.parse src with
  | Error e -> Error { stage = "parse"; message = e.message; line = e.line; col = e.col }
  | Ok named -> (
    try Ok (k named) with
    | Adt.Error (m, loc) -> Error (at "adt" loc m)
    | Debruijn.Error (m, loc) -> Error (at "scope" loc m)
    | Sugar.Error (m, loc) -> Error (at "desugar" loc m)
    | Sce_core.Elab.Elab_error m -> Error (whole "elaborate" m)
    | Core_lambdae.Check.Type_error m -> Error (whole "typecheck" m)
    | Sepcomp.Error m -> Error (whole "unit" m)
    | Failure m -> Error (whole "runtime" (strip_error_prefix m)))

(* resolve -> desugar -> elaborate -> check, shared by every entry point. *)
let core_stages (named : Ast.named) : S.typ * S.exp * C.typ * C.exp =
  let indexed = Debruijn.resolve (Adt.expand named) in
  let sce_typ, sce_exp = Sugar.desugar_program indexed in
  let _, core_exp = Sce_core.Elab.elab S.TTop sce_exp in
  let core_typ = Core_lambdae.Check.typecheck core_exp in
  (sce_typ, sce_exp, core_typ, core_exp)

let run (src : string) : (outcome, error) result =
  staged src (fun named ->
    let sce_typ, sce_exp, core_typ, core_exp = core_stages named in
    let value = Core_lambdae.Eval.eval C.Unit core_exp in
    { sce_typ; sce_exp; core_typ; core_exp; value })

let render ~src (e : error) =
  Driver.render ~src
    { Driver.message = e.stage ^ " error: " ^ e.message; line = e.line; col = e.col }

(* Convenience for the REPL and the playground. *)
let type_string (o : outcome) = Sce_core.Pretty.typ_to_string o.sce_typ
let value_string (o : outcome) = Core_lambdae.Pretty.exp_to_string o.value
let core_string (o : outcome) = Core_lambdae.Pretty.exp_to_string o.core_exp

(* The elaborated λE term, without evaluating it — what the wasm backend
   compiles, so a program that diverges at runtime can still be compiled. *)
let run_to_core (src : string) : (C.exp, error) result =
  staged src (fun named ->
    let _, _, _, core_exp = core_stages named in
    core_exp)

(* ---------------- separate compilation ---------------- *)

(* Compile one source file as a unit: resolve its import headers (against
   .scei files living next to it), wrap the declarations as a sandboxed
   struct/functor, and push the result through the unchanged pipeline. Also
   returns the generated interface texts, one per exported module. *)
let compile_unit ~(path : string) (src : string) :
    (Sepcomp.artifact * (string * string) list, error) result =
  staged src (fun p ->
    let dir = Filename.dirname path in
    let imports =
      List.map
        (fun (b, isrc) ->
          try (b, Sepcomp.import_typ ~dir b isrc)
          with Sepcomp.Error m -> raise (Debruijn.Error (m, b.Ast.bd_loc)))
        p.imports
    in
    let t, _, _, core = core_stages (Sepcomp.unit_wrapper imports p) in
    let a_imports, a_exports = Sepcomp.unit_info t in
    let name = Filename.remove_extension (Filename.basename path) in
    let sceis =
      List.filter_map
        (fun d ->
          match d.Ast.it with
          | Ast.DModule (b, _) -> (
            match Sce_core.Elab.srlookup_opt a_exports b.Ast.bd_name with
            | Some ft ->
              Some (b.Ast.bd_name ^ ".scei", Sepcomp.print_typ ft ^ "\n")
            | None -> None)
          | _ -> None)
        p.decls
    in
    ({ Sepcomp.a_name = name; a_imports; a_exports; a_core = core }, sceis))

let link_artifacts (arts : Sepcomp.artifact list) :
    (Sepcomp.artifact, error) result =
  try Ok (Sepcomp.link arts) with Sepcomp.Error m -> Error (whole "link" m)

(* Evaluate a linked artifact: project `main` if it exports one. *)
let run_artifact (a : Sepcomp.artifact) : (string * string, error) result =
  try
    let t, term = Sepcomp.runnable a in
    let v = Core_lambdae.Eval.eval C.Unit term in
    Ok (Sce_core.Pretty.typ_to_string t, Core_lambdae.Pretty.exp_to_string v)
  with
  | Sepcomp.Error m -> Error (whole "link" m)
  | Failure m -> Error (whole "runtime" (strip_error_prefix m))
