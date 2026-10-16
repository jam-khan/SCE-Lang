(** Expansion of algebraic data declarations and constructor matches. *)

val expand : Ast.program -> Ast.program
(** Replace ADTs, constructor uses and matches with aliases, unions and core
    surface forms. Constructors follow type declaration scope and are shadowed
    by value binders. Raises {!Err.Error} for invalid constructor uses or matches. *)
