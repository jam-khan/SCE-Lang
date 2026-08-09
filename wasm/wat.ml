(* Ir.modul -> WAT text.

   Purely for humans: every emitted module can be dumped alongside the binary
   when a test fails, without reaching for a disassembler. `wasm-dis` remains
   the authority on what the *binary* actually says. *)

open Ir

let buf_add = Buffer.add_string

let valtype_str I32 = "i32"

let blocktype_str = function [] -> "" | ts -> " (result " ^ String.concat " " (List.map valtype_str ts) ^ ")"

let memarg_str { offset } = if offset = 0 then "" else Printf.sprintf " offset=%d" offset

let rec instr buf indent i =
  let pad = String.make indent ' ' in
  let line s = buf_add buf (pad ^ s ^ "\n") in
  match i with
  | Const n -> line (Printf.sprintf "i32.const %d" n)
  | Add -> line "i32.add"
  | Sub -> line "i32.sub"
  | Mul -> line "i32.mul"
  | Div_s -> line "i32.div_s"
  | Rem_s -> line "i32.rem_s"
  | Eq -> line "i32.eq"
  | Ne -> line "i32.ne"
  | Lt_s -> line "i32.lt_s"
  | Gt_s -> line "i32.gt_s"
  | Le_s -> line "i32.le_s"
  | Ge_s -> line "i32.ge_s"
  | Eqz -> line "i32.eqz"
  | And -> line "i32.and"
  | Or -> line "i32.or"
  | Load m -> line ("i32.load" ^ memarg_str m)
  | Load8_u m -> line ("i32.load8_u" ^ memarg_str m)
  | Store m -> line ("i32.store" ^ memarg_str m)
  | Store8 m -> line ("i32.store8" ^ memarg_str m)
  | Local_get i -> line (Printf.sprintf "local.get %d" i)
  | Local_set i -> line (Printf.sprintf "local.set %d" i)
  | Local_tee i -> line (Printf.sprintf "local.tee %d" i)
  | Global_get i -> line (Printf.sprintf "global.get %d" i)
  | Global_set i -> line (Printf.sprintf "global.set %d" i)
  | Call i -> line (Printf.sprintf "call %d" i)
  | Call_indirect t -> line (Printf.sprintf "call_indirect (type %d)" t)
  | Br l -> line (Printf.sprintf "br %d" l)
  | Br_if l -> line (Printf.sprintf "br_if %d" l)
  | Return -> line "return"
  | Drop -> line "drop"
  | Unreachable -> line "unreachable"
  | Memory_size -> line "memory.size"
  | Memory_grow -> line "memory.grow"
  | If (bt, thn, els) ->
    line ("if" ^ blocktype_str bt);
    List.iter (instr buf (indent + 2)) thn;
    if els <> [] then begin
      line "else";
      List.iter (instr buf (indent + 2)) els
    end;
    line "end"
  | Block (bt, body) ->
    line ("block" ^ blocktype_str bt);
    List.iter (instr buf (indent + 2)) body;
    line "end"
  | Loop (bt, body) ->
    line ("loop" ^ blocktype_str bt);
    List.iter (instr buf (indent + 2)) body;
    line "end"

let escape s =
  let b = Buffer.create (String.length s + 8) in
  String.iter
    (fun c ->
      let code = Char.code c in
      if c = '"' || c = '\\' then Buffer.add_string b (Printf.sprintf "\\%c" c)
      else if code < 0x20 || code >= 0x7f then
        Buffer.add_string b (Printf.sprintf "\\%02x" code)
      else Buffer.add_char b c)
    s;
  Buffer.contents b

let modul (m : modul) : string =
  let buf = Buffer.create 4096 in
  buf_add buf "(module\n";
  List.iteri
    (fun i { params; results } ->
      buf_add buf
        (Printf.sprintf "  (type %d (func%s%s))\n" i
           (if params = [] then ""
            else " (param " ^ String.concat " " (List.map valtype_str params) ^ ")")
           (if results = [] then ""
            else " (result " ^ String.concat " " (List.map valtype_str results) ^ ")")))
    m.m_types;
  buf_add buf (Printf.sprintf "  (memory %d)\n" m.m_pages);
  if m.m_table > 0 then buf_add buf (Printf.sprintf "  (table %d funcref)\n" m.m_table);
  List.iteri
    (fun i g ->
      buf_add buf
        (Printf.sprintf "  (global %d ;; $%s\n    %s (i32.const %d))\n" i g.gl_name
           (if g.gl_mut then "(mut i32)" else "i32")
           g.gl_init))
    m.m_globals;
  List.iter
    (fun d ->
      buf_add buf (Printf.sprintf "  (data (i32.const %d) \"%s\")\n" d.da_offset (escape d.da_bytes)))
    m.m_datas;
  if m.m_elems <> [] then
    buf_add buf
      (Printf.sprintf "  (elem (i32.const 0) %s)\n"
         (String.concat " " (List.map string_of_int m.m_elems)));
  List.iteri
    (fun i f ->
      buf_add buf (Printf.sprintf "  (func %d ;; $%s  (type %d)\n" i f.fn_name f.fn_type);
      if f.fn_locals <> [] then
        buf_add buf
          (Printf.sprintf "    (local %s)\n"
             (String.concat " " (List.map valtype_str f.fn_locals)));
      List.iter (instr buf 4) f.fn_body;
      buf_add buf "  )\n")
    m.m_funcs;
  List.iter
    (fun e ->
      let d =
        match e.ex_desc with
        | ExFunc i -> Printf.sprintf "(func %d)" i
        | ExTable i -> Printf.sprintf "(table %d)" i
        | ExMemory i -> Printf.sprintf "(memory %d)" i
        | ExGlobal i -> Printf.sprintf "(global %d)" i
      in
      buf_add buf (Printf.sprintf "  (export \"%s\" %s)\n" e.ex_name d))
    m.m_exports;
  buf_add buf ")\n";
  Buffer.contents buf
