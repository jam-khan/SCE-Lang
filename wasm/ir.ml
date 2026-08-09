(* A small WebAssembly module IR — just the subset the λE backend emits.

   Both the binary encoder (Emit) and the text printer (Wat) consume this, so
   the two cannot describe different modules. Everything is i32: λE values are
   pointers into linear memory, and the only unboxed quantities are the
   payloads inside a cell. *)

type valtype = I32

type functype = { params : valtype list; results : valtype list }

(* A memory access: byte offset folded into the instruction, natural alignment. *)
type memarg = { offset : int }

type instr =
  | Const of int
  | Add | Sub | Mul | Div_s | Rem_s
  | Eq | Ne | Lt_s | Le_s | Gt_s | Ge_s
  | Eqz
  | And | Or
  | Load of memarg          (* i32.load       *)
  | Load8_u of memarg       (* i32.load8_u    *)
  | Store of memarg         (* i32.store      *)
  | Store8 of memarg        (* i32.store8     *)
  | Local_get of int
  | Local_set of int
  | Local_tee of int
  | Global_get of int
  | Global_set of int
  | Call of int
  | Call_indirect of int    (* type index; table 0 *)
  | If of valtype list * instr list * instr list
  | Block of valtype list * instr list
  | Loop of valtype list * instr list
  | Br of int
  | Br_if of int
  | Return
  | Drop
  | Unreachable
  | Memory_size
  | Memory_grow

type func = {
  fn_name : string;         (* for readable WAT and error messages *)
  fn_type : int;            (* index into the type section *)
  fn_locals : valtype list; (* declared after the parameters *)
  fn_body : instr list;
}

type global = { gl_name : string; gl_mut : bool; gl_init : int }

type exportdesc = ExFunc of int | ExTable of int | ExMemory of int | ExGlobal of int

type export = { ex_name : string; ex_desc : exportdesc }

type data = { da_offset : int; da_bytes : string }

type modul = {
  m_types : functype list;
  m_funcs : func list;
  m_table : int;            (* number of entries; 0 means no table *)
  m_elems : int list;       (* function indices, laid out from table offset 0 *)
  m_pages : int;            (* initial memory size, in 64KiB pages *)
  m_globals : global list;
  m_exports : export list;
  m_datas : data list;
}

let empty_module =
  {
    m_types = [];
    m_funcs = [];
    m_table = 0;
    m_elems = [];
    m_pages = 1;
    m_globals = [];
    m_exports = [];
    m_datas = [];
  }

(* Types are interned so the same signature is not emitted twice; the backend
   only ever needs a handful. *)
let type_index (types : functype list ref) (t : functype) : int =
  let rec find i = function
    | [] ->
      types := !types @ [ t ];
      i
    | t' :: rest -> if t' = t then i else find (i + 1) rest
  in
  find 0 !types

let load ?(offset = 0) () = Load { offset }
let store ?(offset = 0) () = Store { offset }
