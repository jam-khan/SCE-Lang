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

let run (src : string) : (outcome, error) result =
  match Driver.parse src with
  | Error e -> Error { stage = "parse"; message = e.message; line = e.line; col = e.col }
  | Ok named -> (
    try
      let indexed = Debruijn.resolve named in
      let sce_typ, sce_exp = Sugar.desugar_program indexed in
      let _, core_exp = Sce_core.Elab.elab S.TTop sce_exp in
      let core_typ = Core_lambdae.Check.typecheck core_exp in
      let value = Core_lambdae.Eval.eval C.Unit core_exp in
      Ok { sce_typ; sce_exp; core_typ; core_exp; value }
    with
    | Debruijn.Error (m, loc) -> Error (at "scope" loc m)
    | Sugar.Error (m, loc) -> Error (at "desugar" loc m)
    | Sce_core.Elab.Elab_error m -> Error (whole "elaborate" m)
    | Core_lambdae.Check.Type_error m -> Error (whole "typecheck" m)
    (* The interpreters raise Failure with their own "Error: " prefix. *)
    | Failure m ->
      let m =
        match String.index_opt m ':' with
        | Some i when String.starts_with ~prefix:"Error:" m ->
          String.trim (String.sub m (i + 1) (String.length m - i - 1))
        | _ -> m
      in
      Error (whole "runtime" m))

let render ~src (e : error) =
  Driver.render ~src
    { Driver.message = e.stage ^ " error: " ^ e.message; line = e.line; col = e.col }

(* Convenience for the REPL and the playground. *)
let type_string (o : outcome) = Sce_core.Pretty.typ_to_string o.sce_typ
let value_string (o : outcome) = Core_lambdae.Pretty.exp_to_string o.value
let core_string (o : outcome) = Core_lambdae.Pretty.exp_to_string o.core_exp
