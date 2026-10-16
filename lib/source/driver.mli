(** Parsing and source diagnostic presentation. *)

type error = {
  message : string;
  line : int; (** One-based source line. *)
  col : int; (** Zero-based byte offset within the line. *)
}

val line_col : Lexing.position -> int * int
(** Source line and byte column; dummy positions retain invalid coordinates. *)

val error_at : Ast.loc -> string -> error
(** Attach a message to the start of a location. *)

val parse : string -> (Ast.program, error) result
(** Parse program text, returning reported lexer and syntax errors as diagnostics. *)

val parse_intf : string -> (Ast.intf, error) result
(** Parse the contents of a [.scei] interface file. *)

val render : src:string -> error -> string
(** Format a diagnostic with its source line and a caret. Invalid coordinates
    from synthesized locations produce the message alone. *)
