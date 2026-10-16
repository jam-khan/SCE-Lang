(** Runtime functions expressed in the shared WebAssembly-GC IR. *)

val funcs : Ir.func list
(** String concatenation/equality, host accessors, and host constructors, in
    [Abi] function-index order. This list excludes [main]. It assumes the shared
    ABI types and unit global; assembling the IR invokes no host code.

    At runtime, accessors may trap on incompatible values or out-of-range byte
    indices. Constructors allocate GC values, except [unitval], which returns
    the unit global; [setStrByte] mutates a string's byte array. *)
