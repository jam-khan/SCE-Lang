(* Ir.modul -> WAT text.

   Purely for humans: every emitted module can be dumped alongside the binary
   when a test fails, without reaching for a disassembler. `wasm-dis` remains
   the authority on what the *binary* actually says. *)

open Ir

let buf_add = Buffer.add_string

let valtype_str = function
  | I32 -> "i32"
  | Ref i -> Printf.sprintf "(ref null $t%d)" i

let blocktype_str = function
  | [] -> ""
  | ts -> " (result " ^ String.concat " " (List.map valtype_str ts) ^ ")"

let storage_str = function
  | St_i32 -> "i32"
  | St_i8 -> "i8"
  | St_ref i -> Printf.sprintf "(ref null $t%d)" i

let field_str { fld; fmut } =
  if fmut then Printf.sprintf "(mut %s)" (storage_str fld) else storage_str fld

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
  | Local_get i -> line (Printf.sprintf "local.get %d" i)
  | Local_set i -> line (Printf.sprintf "local.set %d" i)
  | Local_tee i -> line (Printf.sprintf "local.tee %d" i)
  | Global_get i -> line (Printf.sprintf "global.get %d" i)
  | Call i -> line (Printf.sprintf "call %d ;; local" i)
  | CallImport i -> line (Printf.sprintf "call %d ;; import" i)
  | CallRef t -> line (Printf.sprintf "call_ref $t%d" t)
  | RefFunc f -> line (Printf.sprintf "ref.func %d" f)
  | RefCast t -> line (Printf.sprintf "ref.cast (ref $t%d)" t)
  | StructNew t -> line (Printf.sprintf "struct.new $t%d" t)
  | StructGet (t, f) -> line (Printf.sprintf "struct.get $t%d %d" t f)
  | ArrayNewDefault t -> line (Printf.sprintf "array.new_default $t%d" t)
  | ArrayNewData (t, d) -> line (Printf.sprintf "array.new_data $t%d %d" t d)
  | ArrayGetU t -> line (Printf.sprintf "array.get_u $t%d" t)
  | ArrayLen -> line "array.len"
  | ArrayCopy (td, ts) -> line (Printf.sprintf "array.copy $t%d $t%d" td ts)
  | Br l -> line (Printf.sprintf "br %d" l)
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

let comptype_str = function
  | CFunc { params; results } ->
    Printf.sprintf "(func%s%s)"
      (if params = [] then ""
       else " (param " ^ String.concat " " (List.map valtype_str params) ^ ")")
      (if results = [] then ""
       else " (result " ^ String.concat " " (List.map valtype_str results) ^ ")")
  | CStruct fs ->
    "(struct "
    ^ String.concat " " (List.map (fun f -> "(field " ^ field_str f ^ ")") fs)
    ^ ")"
  | CArray f -> "(array " ^ field_str f ^ ")"

let modul (m : modul) : string =
  let buf = Buffer.create 4096 in
  buf_add buf "(module\n  (rec\n";
  List.iteri
    (fun i { super; sfinal; comp } ->
      let sub =
        match (super, sfinal) with
        | None, true -> comptype_str comp
        | None, false -> Printf.sprintf "(sub %s)" (comptype_str comp)
        | Some s, true -> Printf.sprintf "(sub final $t%d %s)" s (comptype_str comp)
        | Some s, false -> Printf.sprintf "(sub $t%d %s)" s (comptype_str comp)
      in
      buf_add buf (Printf.sprintf "    (type $t%d %s)\n" i sub))
    m.m_types;
  buf_add buf "  )\n";
  List.iteri
    (fun i (md, nm, ty) ->
      buf_add buf (Printf.sprintf "  (import %S %S (func ;; %d\n    (type $t%d)))\n" md nm i ty))
    m.m_imports;
  List.iteri
    (fun i g ->
      buf_add buf
        (Printf.sprintf "  (global %d ;; $%s\n    %s\n" i g.gl_name
           (if g.gl_mut then Printf.sprintf "(mut %s)" (valtype_str g.gl_type)
            else valtype_str g.gl_type));
      List.iter (instr buf 4) g.gl_init;
      buf_add buf "  )\n")
    m.m_globals;
  List.iteri
    (fun i d ->
      buf_add buf (Printf.sprintf "  (data %d \"%s\")\n" i (escape d)))
    m.m_datas;
  if m.m_declared <> [] then
    buf_add buf
      (Printf.sprintf "  (elem declare func %s)\n"
         (String.concat " " (List.map string_of_int m.m_declared)));
  List.iteri
    (fun i f ->
      buf_add buf (Printf.sprintf "  (func %d ;; $%s  (type $t%d)\n" i f.fn_name f.fn_type);
      if f.fn_locals <> [] then
        buf_add buf
          (Printf.sprintf "    (local %s)\n"
             (String.concat " " (List.map valtype_str f.fn_locals)));
      List.iter (instr buf 4) f.fn_body;
      buf_add buf "  )\n")
    m.m_funcs;
  List.iter
    (fun e -> buf_add buf (Printf.sprintf "  (export \"%s\" (func %d))\n" e.ex_name e.ex_func))
    m.m_exports;
  List.iter
    (fun (n, _) -> buf_add buf (Printf.sprintf "  ;; custom section %S\n" n))
    m.m_customs;
  buf_add buf ")\n";
  Buffer.contents buf
