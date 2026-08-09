(* Ir.modul -> a WebAssembly binary.

   Targets the 1.0 core instruction set only: no bulk memory, no reference
   types beyond funcref, no GC. That keeps the output acceptable to every
   engine and to binaryen's validator. *)

open Ir
open Encode

let valtype buf I32 = byte buf 0x7f

let blocktype buf = function
  | [] -> byte buf 0x40 (* empty *)
  | [ t ] -> valtype buf t
  | _ -> failwith "emit: multi-value blocks are not used by this backend"

let memarg buf { offset } =
  u32 buf 2 (* alignment 2^2 = 4 bytes; every cell field is word-aligned *);
  u32 buf offset

let memarg8 buf { offset } =
  u32 buf 0 (* byte access *);
  u32 buf offset

let rec instr buf = function
  | Const n -> byte buf 0x41; s32 buf n
  | Add -> byte buf 0x6a
  | Sub -> byte buf 0x6b
  | Mul -> byte buf 0x6c
  | Div_s -> byte buf 0x6d
  | Rem_s -> byte buf 0x6f
  | Eq -> byte buf 0x46
  | Ne -> byte buf 0x47
  | Lt_s -> byte buf 0x48
  | Gt_s -> byte buf 0x4a
  | Le_s -> byte buf 0x4c
  | Ge_s -> byte buf 0x4e
  | Eqz -> byte buf 0x45
  | And -> byte buf 0x71
  | Or -> byte buf 0x72
  | Load m -> byte buf 0x28; memarg buf m
  | Load8_u m -> byte buf 0x2d; memarg8 buf m
  | Store m -> byte buf 0x36; memarg buf m
  | Store8 m -> byte buf 0x3a; memarg8 buf m
  | Local_get i -> byte buf 0x20; u32 buf i
  | Local_set i -> byte buf 0x21; u32 buf i
  | Local_tee i -> byte buf 0x22; u32 buf i
  | Global_get i -> byte buf 0x23; u32 buf i
  | Global_set i -> byte buf 0x24; u32 buf i
  | Call i -> byte buf 0x10; u32 buf i
  | Call_indirect t -> byte buf 0x11; u32 buf t; u32 buf 0
  | If (bt, thn, els) ->
    byte buf 0x04;
    blocktype buf bt;
    List.iter (instr buf) thn;
    if els <> [] then begin
      byte buf 0x05;
      List.iter (instr buf) els
    end;
    byte buf 0x0b
  | Block (bt, body) ->
    byte buf 0x02; blocktype buf bt; List.iter (instr buf) body; byte buf 0x0b
  | Loop (bt, body) ->
    byte buf 0x03; blocktype buf bt; List.iter (instr buf) body; byte buf 0x0b
  | Br l -> byte buf 0x0c; u32 buf l
  | Br_if l -> byte buf 0x0d; u32 buf l
  | Return -> byte buf 0x0f
  | Drop -> byte buf 0x1a
  | Unreachable -> byte buf 0x00
  | Memory_size -> byte buf 0x3f; byte buf 0x00
  | Memory_grow -> byte buf 0x40; byte buf 0x00

let functype buf { params; results } =
  byte buf 0x60;
  vec buf valtype params;
  vec buf valtype results

(* Consecutive locals of the same type are run-length encoded; we only have
   i32, so this is a single run. *)
let locals buf ls =
  if ls = [] then u32 buf 0
  else begin
    u32 buf 1;
    u32 buf (List.length ls);
    valtype buf I32
  end

let code buf f =
  let body = Buffer.create 256 in
  locals body f.fn_locals;
  List.iter (instr body) f.fn_body;
  byte body 0x0b (* end *);
  u32 buf (Buffer.length body);
  Buffer.add_buffer buf body

let limits buf min = byte buf 0x00; u32 buf min

let global buf g =
  valtype buf I32;
  byte buf (if g.gl_mut then 0x01 else 0x00);
  byte buf 0x41;
  s32 buf g.gl_init;
  byte buf 0x0b

let export buf e =
  name buf e.ex_name;
  match e.ex_desc with
  | ExFunc i -> byte buf 0x00; u32 buf i
  | ExTable i -> byte buf 0x01; u32 buf i
  | ExMemory i -> byte buf 0x02; u32 buf i
  | ExGlobal i -> byte buf 0x03; u32 buf i

let data buf d =
  byte buf 0x00 (* active, memory 0 *);
  byte buf 0x41;
  s32 buf d.da_offset;
  byte buf 0x0b;
  u32 buf (String.length d.da_bytes);
  Buffer.add_string buf d.da_bytes

let modul (m : modul) : string =
  let buf = Buffer.create 4096 in
  Buffer.add_string buf magic;
  Buffer.add_string buf version;
  section buf 1 (fun b -> vec b functype m.m_types);
  section buf 3 (fun b -> vec b (fun b f -> u32 b f.fn_type) m.m_funcs);
  if m.m_table > 0 then
    section buf 4 (fun b ->
        u32 b 1;
        byte b 0x70 (* funcref *);
        limits b m.m_table);
  section buf 5 (fun b -> u32 b 1; limits b m.m_pages);
  section buf 6 (fun b -> vec b global m.m_globals);
  section buf 7 (fun b -> vec b export m.m_exports);
  if m.m_elems <> [] then
    section buf 9 (fun b ->
        u32 b 1;
        byte b 0x00 (* active, table 0 *);
        byte b 0x41;
        s32 b 0;
        byte b 0x0b;
        vec b (fun b i -> u32 b i) m.m_elems);
  section buf 10 (fun b -> vec b code m.m_funcs);
  section buf 11 (fun b -> vec b data m.m_datas);
  Buffer.contents buf
