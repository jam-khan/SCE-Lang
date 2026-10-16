(** Located diagnostics shared by source passes. *)

exception Error of string * Ast.loc

val err : Ast.loc -> ('a, unit, string, 'b) format4 -> 'a
(** Format a message and raise {!Error} at the supplied location. *)

val lift : Ast.loc -> (unit -> 'a) -> 'a
(** Run a judgement helper, translating [Sce_core.Elab.Elab_error] to
    {!Error} at the supplied location. Other exceptions propagate. *)

val check_unique : string -> (string * Ast.loc) list -> unit
(** [check_unique what labels] raises {!Error} at the first label with a later
    duplicate. [what] identifies the construct in the diagnostic. *)
