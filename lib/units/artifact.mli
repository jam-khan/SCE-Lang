(** Compiled units and their serialized [.sceo] and textual [.scei] formats. *)

exception Error of string
(** An invalid interface, incompatible artifact, or linking error. *)

val err : ('a, unit, string, 'b) format4 -> 'a
(** Raise {!Error} with a formatted message. *)

type t = {
  a_name : string;                 (** Unit name used in diagnostics and Wasm linking. *)
  a_imports : Sce_core.Ast.typ option;
      (** Import record type; [None] for an import-free unit. *)
  a_exports : Sce_core.Ast.typ;
  a_core : Core_lambdae.Ast.exp;    (** Closed core structure or import function. *)
}
(** The core term has the elaboration of {!slot_typ} as its type. Compilation
    establishes this invariant; constructing a record does not check it. *)

val slot_typ : t -> Sce_core.Ast.typ
(** The exports type for an import-free unit, or its functor type otherwise. *)

val save : string -> t -> unit
(** Write a format marker and an OCaml-marshaled artifact.
    Raises [Sys_error] on file I/O failure. *)

val load : string -> t
(** Read an artifact produced by a compatible compiler. Checks the format
    marker, but does not validate marshaled contents; input must be trusted.
    @raise Error if the file cannot be opened or its format marker differs.
    Truncated or malformed contents may raise standard I/O or Marshal
    exceptions. *)

val print_typ : Sce_core.Ast.typ -> string
(** Print a closed type in interface syntax, choosing names for recursive
    binders. Labels must be valid surface identifiers for {!parse_typ} to
    recover the original type.
    @raise Error if a recursive type variable is unbound. *)

val expand_aliases : Ast.intf -> Ast.typ
(** Expand interface aliases in declaration order. Recursive binders shadow
    aliases of the same name. *)

val parse_typ : what:string -> string -> Sce_core.Ast.typ
(** Parse an interface, expand aliases, and resolve recursive type variables.
    [what] identifies the input in parse diagnostics.
    @raise Error on a parse error.
    @raise Err.Error if type conversion fails. *)
