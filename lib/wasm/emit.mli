(** Binary emission for the WebAssembly-GC IR. *)

val modul : Ir.modul -> string
(** Encode a module with one type recursion group, passive data segments, and
    the supplied custom sections. Local function indices are shifted past
    imports. Returns binary bytes without executing the module or writing files.

    The caller supplies well-formed, well-typed IR. Raises [Failure] for a
    structured instruction with more than one result; indices, integer ranges,
    and instruction typing are otherwise not validated. *)
