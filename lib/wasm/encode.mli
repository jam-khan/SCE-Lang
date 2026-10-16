(** Append binary encoding primitives to buffers. Numeric ranges are caller
    preconditions: the helpers do not check WebAssembly integer bounds. *)

val u32 : Buffer.t -> int -> unit
(** Append unsigned LEB128. The argument must be nonnegative and fit in an
    unsigned 32-bit integer. *)

val s32 : Buffer.t -> int -> unit
(** Append signed LEB128. Use a signed 32-bit argument for an [i32] immediate. *)

val byte : Buffer.t -> int -> unit
(** Append the low eight bits. *)

val vec : Buffer.t -> (Buffer.t -> 'a -> unit) -> 'a list -> unit
(** Append the element count, then encode each element in order. *)

val name : Buffer.t -> string -> unit
(** Append a byte length followed by the string bytes; no UTF-8 validation. *)

val section : Buffer.t -> int -> (Buffer.t -> unit) -> unit
(** Build the payload in a fresh buffer, then append its section identifier,
    byte length, and bytes. Omit the section if the payload buffer is empty.
    If the callback raises, no section bytes are appended to the destination. *)

val magic : string
(** WebAssembly magic bytes. *)

val version : string
(** Binary format version bytes. *)
