(** Source compilation and evaluation for the CLI and playground.

    Language errors are returned with their compilation stage. File I/O
    exceptions and malformed serialized artifacts can still escape. *)

type error = {
  stage : string;
  message : string;
  line : int;  (** One-based line number. *)
  col : int;   (** Zero-based byte offset within the line. *)
}
(** Stages without source locations report line 1, column 0. *)

type outcome = {
  sce_typ : Sce_core.Ast.typ;
  sce_exp : Sce_core.Ast.nameless;
  core_typ : Core_lambdae.Ast.typ;
  core_exp : Core_lambdae.Ast.exp;
  value : Core_lambdae.Ast.exp;
}
(** Resolved source and elaborated core terms, the source type synthesized
    during desugaring, the independently checked core type, and the result. *)

val run : string -> (outcome, error) result
(** Parse, desugar, resolve, elaborate, typecheck, and evaluate a program under
    the empty environment. Evaluation may diverge or invoke host capabilities. *)

val run_to_core : string -> (Core_lambdae.Ast.exp, error) result
(** Compile and typecheck without evaluating the resulting term. *)

val render : src:string -> error -> string
(** Format a diagnostic with its source line and a caret. *)

val type_string : outcome -> string
(** Format the source type. *)

val value_string : outcome -> string
(** Format the evaluation result. *)

val core_string : outcome -> string
(** Format the elaborated core term. *)

val compile_unit :
  path:string -> string ->
  (Units.Artifact.t * (string * string) list, error) result
(** Compile a source file as a closed structure or sandboxed functor.
    [path] supplies the unit name and directory for resolving interfaces.
    Existing [.scei] files are checked; missing exported module interfaces are
    returned as [(filename, contents)] pairs. This function writes no files. *)

val link_artifacts : Units.Artifact.t list -> (Units.Artifact.t, error) result
(** Link units in dependency order and typecheck the resulting core term.
    The first unit must have no imports. No unit is evaluated. *)

val run_artifact : Units.Artifact.t -> (string * string, error) result
(** Evaluate an artifact with no outstanding imports, selecting [main] when
    uniquely exported. Return the formatted type and value. Evaluation may
    diverge or invoke host capabilities. *)
