(** Shared value layout and fixed indices for the compiler, runtime, and
    JavaScript host. Every value struct extends [ty_val], with its tag in field
    zero. Values with the same layout may have different tags. *)

val tag_int : int
val tag_bool : int
val tag_str : int
val tag_unit : int
val tag_mrg : int
val tag_lrec : int
val tag_clos : int
val tag_fclos : int
val tag_inl : int
val tag_inr : int
val tag_fold : int

(** Indices in [typedefs], the shared recursion group. *)
val ty_val : int
val ty_i32box : int
val ty_bytes : int
val ty_str : int
val ty_pair : int
val ty_lrec : int
val ty_fn : int
(** Closure body signature: [(self, argument) -> value]. *)

val ty_clos : int
val ty_wrap : int
val ty_v2v : int
(** [(value) -> value]. *)

val ty_v2i : int
(** [(value) -> i32]. *)

val ty_vi2i : int
(** [(value, i32) -> i32]. *)

val ty_0v : int
(** [() -> value]. *)

val ty_vv2i : int
(** [(value, value) -> i32]. *)

val ty_i2v : int
(** [(i32) -> value]. *)

val ty_vii2n : int
(** [(value, i32, i32) -> ()]. *)

val typedefs : Ir.subtype list
(** Ordered types shared by all compiled modules. [ty_bytes] is a mutable
    packed-byte array; struct fields are immutable. Reference types are
    nullable so locals can be default-initialized. *)

val p_a : int
(** Field one: number, bytes, pair left, label bytes, closure function, or
    wrapped value, according to the struct type. *)

val p_b : int
(** Field two: pair right, labelled value, or closure environment. *)

(** Local function indices, excluding imports. Runtime functions precede
    [fn_main]; lifted closures follow it. *)
val fn_strcat : int
val fn_streq : int
val fn_tag : int
val fn_num : int
val fn_str_len : int
val fn_str_byte : int
val fn_pair_a : int
val fn_pair_b : int
val fn_lrec_name_len : int
val fn_lrec_name_byte : int
val fn_lrec_val : int
val fn_wrap_val : int
val fn_unitval : int
val fn_new_str : int
val fn_set_str_byte : int
val fn_inl : int
val fn_inr : int
val fn_lrec : int
val fn_main : int

val runtime_count : int
(** Number of reserved local function slots, including [main]. *)

val exports : (string * int) list
(** Host-visible export names paired with local function indices. Includes
    [main], value accessors, and constructors used by host capabilities. *)

val gl_unit : int
(** Index of the immutable global holding the unit value. *)

val strings_data : int
(** Passive segment index for pooled literal and label bytes. The compiler
    omits the segment when the pool is empty. *)
