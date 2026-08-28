(* parse -> desugar -> resolve -> elaborate -> check -> evaluate, with every
   stage's failure rendered the same way. *)

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
  sce_exp : S.nameless; (* the λSCE term *)
  core_typ : C.typ;     (* the type λE independently assigns to the elaboration *)
  core_exp : C.exp;     (* the elaborated λE term *)
  value : C.exp;        (* the result of evaluating it *)
}

let at stage (loc : Ast.loc) message =
  let line, col = Driver.line_col loc.start_p in
  { stage; message; line; col }

(* Stages past the surface AST have no position of their own. *)
let whole stage message = { stage; message; line = 1; col = 0 }

(* The interpreters raise Failure with their own "Error: " prefix. *)
let strip_error_prefix m =
  let p = "Error: " in
  if String.starts_with ~prefix:p m then
    String.sub m (String.length p) (String.length m - String.length p)
  else m

(* Parse, then run `k` with every later stage's exception mapped to `error`. *)
let staged (src : string) (k : Ast.program -> 'a) : ('a, error) result =
  match Driver.parse src with
  | Error e -> Error { stage = "parse"; message = e.message; line = e.line; col = e.col }
  | Ok named -> (
    try Ok (k named) with
    | Adt.Error (m, loc) -> Error (at "adt" loc m)
    | Sugar.Error (m, loc) -> Error (at "desugar" loc m)
    (* Sugar resolved every name, so this only fires on a front-end bug. *)
    | Sce_core.Debruijn.Error m -> Error (whole "internal" m)
    | Sce_core.Elab.Elab_error m -> Error (whole "elaborate" m)
    | Core_lambdae.Check.Type_error m -> Error (whole "typecheck" m)
    | Failure m -> Error (whole "runtime" (strip_error_prefix m)))

(* desugar -> resolve -> elaborate -> check, shared by every entry point. *)
let core_stages (p : Ast.program) : S.typ * S.nameless * C.typ * C.exp =
  let sce_typ, named = Sugar.desugar_program (Adt.expand p) in
  let sce_exp = Sce_core.Debruijn.resolve named in
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
