(* Ir.modul -> a WebAssembly binary.

   Targets WasmGC (the typed-references + GC proposals, standardized in wasm
   3.0): struct/array types in one recursion group, ref.cast, call_ref, and
   passive data read through array.new_data. No linear memory, no tables. *)

open Ir
open Encode

(* Heap-type indices are signed LEB (s33); ours are tiny non-negatives, for
   which s32 produces the identical bytes. *)
let s33 = s32

let valtype buf = function
  | I32 -> byte buf 0x7f
  | Ref i -> byte buf 0x63 (* (ref null $i) *); s33 buf i

let blocktype buf = function
  | [] -> byte buf 0x40
  | [ t ] -> valtype buf t
  | _ -> failwith "emit: multi-value blocks are not used by this backend"

let storage buf = function
  | St_i32 -> byte buf 0x7f
  | St_i8 -> byte buf 0x78
  | St_ref i -> byte buf 0x63; s33 buf i

let field buf { fld; fmut } =
  storage buf fld;
  byte buf (if fmut then 0x01 else 0x00)

let functype buf { params; results } =
  byte buf 0x60;
  vec buf valtype params;
  vec buf valtype results

let comptype buf = function
  | CFunc ft -> functype buf ft
  | CStruct fs -> byte buf 0x5f; vec buf field fs
  | CArray f -> byte buf 0x5e; field buf f

let subtype buf { super; sfinal; comp } =
  match (super, sfinal) with
  | None, true -> comptype buf comp (* plain comptype means final, no supers *)
  | None, false -> byte buf 0x50; u32 buf 0; comptype buf comp
  | Some s, true -> byte buf 0x4f; u32 buf 1; u32 buf s; comptype buf comp
  | Some s, false -> byte buf 0x50; u32 buf 1; u32 buf s; comptype buf comp

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
  | Local_get i -> byte buf 0x20; u32 buf i
  | Local_set i -> byte buf 0x21; u32 buf i
  | Local_tee i -> byte buf 0x22; u32 buf i
  | Global_get i -> byte buf 0x23; u32 buf i
  | Call i -> byte buf 0x10; u32 buf i
  | CallRef t -> byte buf 0x14; u32 buf t
  | RefFunc f -> byte buf 0xd2; u32 buf f
  | RefCast t -> byte buf 0xfb; u32 buf 0x16; s33 buf t
  | StructNew t -> byte buf 0xfb; u32 buf 0x00; u32 buf t
  | StructGet (t, f) -> byte buf 0xfb; u32 buf 0x02; u32 buf t; u32 buf f
  | ArrayNewDefault t -> byte buf 0xfb; u32 buf 0x07; u32 buf t
  | ArrayNewData (t, d) -> byte buf 0xfb; u32 buf 0x09; u32 buf t; u32 buf d
  | ArrayGetU t -> byte buf 0xfb; u32 buf 0x0d; u32 buf t
  | ArrayLen -> byte buf 0xfb; u32 buf 0x0f
  | ArrayCopy (td, ts) -> byte buf 0xfb; u32 buf 0x11; u32 buf td; u32 buf ts
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

(* Consecutive locals of the same type are run-length encoded. *)
let locals buf ls =
  let groups =
    List.fold_left
      (fun acc t ->
        match acc with
        | (t', n) :: rest when t' = t -> (t', n + 1) :: rest
        | _ -> (t, 1) :: acc)
      [] ls
    |> List.rev
  in
  u32 buf (List.length groups);
  List.iter
    (fun (t, n) ->
      u32 buf n;
      valtype buf t)
    groups

let code buf f =
  let body = Buffer.create 256 in
  locals body f.fn_locals;
  List.iter (instr body) f.fn_body;
  byte body 0x0b;
  u32 buf (Buffer.length body);
  Buffer.add_buffer buf body

let global buf g =
  valtype buf g.gl_type;
  byte buf (if g.gl_mut then 0x01 else 0x00);
  List.iter (instr buf) g.gl_init;
  byte buf 0x0b

let export buf e =
  name buf e.ex_name;
  byte buf 0x00;
  u32 buf e.ex_func

let modul (m : modul) : string =
  let buf = Buffer.create 4096 in
  Buffer.add_string buf magic;
  Buffer.add_string buf version;
  (* one recursion group holding every type, so mutual references just work *)
  section buf 1 (fun b ->
      u32 b 1;
      byte b 0x4e;
      vec b subtype m.m_types);
  section buf 3 (fun b -> vec b (fun b f -> u32 b f.fn_type) m.m_funcs);
  section buf 6 (fun b -> vec b global m.m_globals);
  section buf 7 (fun b -> vec b export m.m_exports);
  (* declarative element segment: the functions ref.func may name *)
  if m.m_declared <> [] then
    section buf 9 (fun b ->
        u32 b 1;
        u32 b 3 (* declarative *);
        byte b 0x00 (* elemkind: func *);
        vec b (fun b i -> u32 b i) m.m_declared);
  (* array.new_data requires the data count to be known before the code section *)
  if m.m_datas <> [] then
    section buf 12 (fun b -> u32 b (List.length m.m_datas));
  section buf 10 (fun b -> vec b code m.m_funcs);
  if m.m_datas <> [] then
    section buf 11 (fun b ->
        vec b
          (fun b bytes ->
            u32 b 1 (* passive *);
            u32 b (String.length bytes);
            Buffer.add_string b bytes)
          m.m_datas);
  List.iter
    (fun (nm, bytes) ->
      section buf 0 (fun b ->
          name b nm;
          Buffer.add_string b bytes))
    m.m_customs;
  Buffer.contents buf
