(** Diagnostic printers. Their output is not a source serialization format. *)

(** Render a type with precedence-aware parentheses and indexed mu variables. *)
val typ_to_string : Ast.typ -> string

(** Render an expression or value, abbreviating function bodies and case
    branches. Fully labelled merges are displayed as records. *)
val exp_to_string : Ast.exp -> string
