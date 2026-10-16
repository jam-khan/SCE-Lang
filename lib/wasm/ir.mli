(** The WebAssembly-GC subset shared by the compiler, binary emitter, and
    diagnostic printer. Indices are zero-based. There is no linear memory or
    function table; all reference value and storage types are nullable. *)

type valtype = I32 | Ref of int
(** [Ref t] denotes [(ref null t)], where [t] indexes [modul.m_types]. *)

type functype = { params : valtype list; results : valtype list }

type storage = St_i32 | St_i8 | St_ref of int
(** [St_i8] is packed array/struct storage; [St_ref t] is a nullable reference
    to type [t]. *)

type field = { fld : storage; fmut : bool }

type comptype =
  | CFunc of functype
  | CStruct of field list
  | CArray of field

type subtype = { super : int option; sfinal : bool; comp : comptype }
(** [super] is an optional type index; [sfinal] prevents further subtyping. *)

type instr =
  | Const of int
  | Add | Sub | Mul | Div_s | Rem_s
  | Eq | Ne | Lt_s | Le_s | Gt_s | Ge_s
  | Eqz
  | Local_get of int
  | Local_set of int
  | Local_tee of int
  | Global_get of int
  | Call of int
      (** Index into [m_funcs], excluding imports. *)
  | CallImport of int
      (** Index into [m_imports]. *)
  | CallRef of int
      (** Function type index. *)
  | RefFunc of int
      (** Local function index, also listed in [m_declared]. *)
  | RefCast of int
      (** Cast to a non-null reference of this type; traps on null or mismatch. *)
  | StructNew of int
  | StructGet of int * int
      (** Type index and field index. *)
  | ArrayNewDefault of int
  | ArrayNewData of int * int
      (** Array type index and passive data segment index. *)
  | ArrayGetU of int
  | ArraySet of int
  | ArrayLen
  | ArrayCopy of int * int
      (** Destination and source array type indices. *)
  | If of valtype list * instr list * instr list
  | Block of valtype list * instr list
  | Loop of valtype list * instr list
  | Br of int
      (** Relative label depth; zero addresses the innermost label. *)
(** Local indices count parameters first, then declared locals. Structured
    instructions carry result types; the binary emitter supports zero or one
    result per block. Other integer type operands index [m_types]. *)

type func = {
  fn_name : string;  (** Diagnostic name. *)
  fn_type : int;  (** Function type index. *)
  fn_locals : valtype list;  (** Locals following the parameters. *)
  fn_body : instr list;
}

type global = {
  gl_name : string;
  gl_type : valtype;
  gl_mut : bool;
  gl_init : instr list;
}

type export = {
  ex_name : string;
  ex_func : int;  (** Local function index, excluding imports. *)
}

type modul = {
  m_types : subtype list;  (** One ordered recursion group. *)
  m_imports : (string * string * int) list;
      (** Module name, import name, and function type index. *)
  m_funcs : func list;  (** Ordered local functions. *)
  m_globals : global list;
  m_exports : export list;
  m_declared : int list;  (** Local functions allowed as [RefFunc] operands. *)
  m_datas : string list;  (** Ordered passive byte segments. *)
  m_customs : (string * string) list;  (** Custom section names and raw payloads. *)
}
(** The binary emitter adds the import count to local function references,
    declarations, and exports. The IR does not itself validate indices or
    instruction typing. *)
