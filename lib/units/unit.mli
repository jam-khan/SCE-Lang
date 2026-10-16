(** Turn source files into closed structures or sandboxed functors. *)

val import_typ : dir:string -> Ast.binder -> Ast.import_source -> Ast.typ
(** Resolve an import's inline type or read its [.scei] file in [dir]. File
    aliases are expanded before entering the importing scope. If the file
    cannot be read, [Sys] and [Str] use their built-in interfaces.
    @raise Units.Artifact.Error if another interface cannot be read or parsed. *)

val wrapper : (Ast.binder * Ast.typ) list -> Ast.program -> Ast.program
(** Package declarations in a sandboxed structure, or a sandboxed functor
    opening the supplied imports. The input's import headers and final
    expression are replaced by this wrapper. *)

val info : Sce_core.Ast.typ -> Sce_core.Ast.typ option * Sce_core.Ast.typ
(** Split a unit's synthesized type into optional imports and exports. *)
