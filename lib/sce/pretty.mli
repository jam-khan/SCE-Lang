(** Diagnostic type printing; output is not a source serialization format. *)

(** Render with precedence-aware parentheses and indexed mu variables. *)
val typ_to_string : Ast.typ -> string
