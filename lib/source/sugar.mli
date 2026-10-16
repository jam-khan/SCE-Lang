(** Lower named surface syntax to named SCE terms. *)

val conv_typ_closed : Ast.typ -> Sce_core.Ast.typ
(** Convert a type with no free type names; aliases must already be expanded.
    Raises {!Err.Error} for unbound names or duplicate record labels. *)

val desugar_program : Ast.program -> Sce_core.Ast.typ * Sce_core.Ast.named
(** Expand ADTs and lower a program without imports. Use its explicit [main]
    expression, its declaration named [main], or a record of its value and
    module declarations, in that order. Returns the inferred type shape and
    term; full type checking remains the elaborator's responsibility.
    Raises {!Err.Error} for source resolution or desugaring errors. *)
