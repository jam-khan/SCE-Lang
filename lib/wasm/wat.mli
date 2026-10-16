(** Human-readable diagnostics for the WebAssembly-GC IR. *)

val modul : Ir.modul -> string
(** Render WAT-like text without executing the module or writing files. Function
    indices retain the IR's local numbering rather than incorporating imports;
    custom sections appear only as name comments. This is diagnostic output,
    not a lossless serialization of the binary module. *)
