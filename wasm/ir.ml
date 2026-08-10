(* A small WebAssembly-GC module IR — just the subset the λE backend emits.

   Both the binary encoder (Emit) and the text printer (Wat) consume this, so
   the two cannot describe different modules. Values are GC struct references;
   the only unboxed quantities are the i32 payloads inside them. There is no
   linear memory and no function table in an emitted module. *)

type valtype =
  | I32
  | Ref of int (* (ref null $t) — everything flows nullable, so any value can
                  land in any local/param without definite-assignment fuss *)

type functype = { params : valtype list; results : valtype list }

(* ---- type-section entries (one recursion group holds them all) ---- *)

type storage = St_i32 | St_i8 | St_ref of int

type field = { fld : storage; fmut : bool }

type comptype =
  | CFunc of functype
  | CStruct of field list
  | CArray of field

type subtype = { super : int option; sfinal : bool; comp : comptype }

(* ---- instructions ---- *)

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
  | CallRef of int             (* call_ref (type $t) *)
  | RefFunc of int             (* needs the function declared in m_declared *)
  | RefCast of int             (* ref.cast (ref $t) — traps on null *)
  | StructNew of int
  | StructGet of int * int     (* type, field *)
  | ArrayNewDefault of int
  | ArrayNewData of int * int  (* type, data segment *)
  | ArrayGetU of int
  | ArrayLen
  | ArrayCopy of int * int     (* dst type, src type *)
  | If of valtype list * instr list * instr list
  | Block of valtype list * instr list
  | Loop of valtype list * instr list
  | Br of int
  | Br_if of int
  | Return
  | Drop
  | Unreachable

type func = {
  fn_name : string;            (* for readable WAT and error messages *)
  fn_type : int;
  fn_locals : valtype list;    (* declared after the parameters *)
  fn_body : instr list;
}

type global = { gl_name : string; gl_type : valtype; gl_mut : bool; gl_init : instr list }

type export = { ex_name : string; ex_func : int }

type modul = {
  m_types : subtype list;      (* emitted as a single recursion group *)
  m_funcs : func list;
  m_globals : global list;
  m_exports : export list;
  m_declared : int list;       (* functions referenced by ref.func *)
  m_datas : string list;       (* passive segments *)
  m_customs : (string * string) list;
}
