(* The contract between the compiler, the emitted runtime, and the host.

   Every λE value is a reference to a GC struct subtyping $Val, whose first
   field is a tag — so the host can render a result without being told its
   type, which is what lets compiled output be diffed against the interpreter.
   JavaScript cannot look inside GC structs, so the module exports accessor
   functions and run.js drives the walk through them. *)

open Ir

(* ---------------- tags ----------------

   Same numbering as the interpreter-side renderer has always used. Types that
   share a struct shape are told apart by tag alone: Int/Bool in $I32Box,
   Clos/Fclos in $Clos, Inl/Inr/Fold in $Wrap. *)

let tag_int = 0
let tag_bool = 1
let tag_str = 2
let tag_unit = 3
let tag_mrg = 4
let tag_lrec = 5
let tag_clos = 6
let tag_fclos = 7
let tag_inl = 8
let tag_inr = 9
let tag_fold = 10

(* ---------------- the type hierarchy ----------------

   $Val    = struct { tag }                     the open supertype
   $I32Box = struct { tag, n }                  Int and Bool
   $Bytes  = array (mut i8)                     string payload
   $Str    = struct { tag, bytes }
   $Pair   = struct { tag, left, right }        Mrg
   $Lrec   = struct { tag, name bytes, value }  label carried in the value
   $Fn     = func (self, arg) -> value
   $Clos   = struct { tag, fn, env }            Clos and Fclos
   $Wrap   = struct { tag, value }              Inl, Inr, Fold *)

let ty_val = 0
let ty_i32box = 1
let ty_bytes = 2
let ty_str = 3
let ty_pair = 4
let ty_lrec = 5
let ty_fn = 6
let ty_clos = 7
let ty_wrap = 8
(* signatures for the runtime and accessors *)
let ty_v2v = 9 (* (val) -> val        *)
let ty_v2i = 10 (* (val) -> i32        *)
let ty_vi2i = 11 (* (val, i32) -> i32   *)
let ty_0v = 12 (* () -> val           *)
let ty_vv2i = 13 (* (val, val) -> i32   *)
let ty_i2v = 14 (* (i32) -> val        *)
let ty_vii2n = 15 (* (val, i32, i32) -> () *)

let f_i32 = { fld = St_i32; fmut = false }
let f_ref t = { fld = St_ref t; fmut = false }
let vref t = Ref t

let typedefs : subtype list =
  [
    { super = None; sfinal = false; comp = CStruct [ f_i32 ] };
    { super = Some ty_val; sfinal = true; comp = CStruct [ f_i32; f_i32 ] };
    { super = None; sfinal = true; comp = CArray { fld = St_i8; fmut = true } };
    { super = Some ty_val; sfinal = true; comp = CStruct [ f_i32; f_ref ty_bytes ] };
    { super = Some ty_val; sfinal = true;
      comp = CStruct [ f_i32; f_ref ty_val; f_ref ty_val ] };
    { super = Some ty_val; sfinal = true;
      comp = CStruct [ f_i32; f_ref ty_bytes; f_ref ty_val ] };
    { super = None; sfinal = true;
      comp = CFunc { params = [ vref ty_val; vref ty_val ]; results = [ vref ty_val ] } };
    { super = Some ty_val; sfinal = true;
      comp = CStruct [ f_i32; f_ref ty_fn; f_ref ty_val ] };
    { super = Some ty_val; sfinal = true; comp = CStruct [ f_i32; f_ref ty_val ] };
    { super = None; sfinal = true;
      comp = CFunc { params = [ vref ty_val ]; results = [ vref ty_val ] } };
    { super = None; sfinal = true;
      comp = CFunc { params = [ vref ty_val ]; results = [ I32 ] } };
    { super = None; sfinal = true;
      comp = CFunc { params = [ vref ty_val; I32 ]; results = [ I32 ] } };
    { super = None; sfinal = true; comp = CFunc { params = []; results = [ vref ty_val ] } };
    { super = None; sfinal = true;
      comp = CFunc { params = [ vref ty_val; vref ty_val ]; results = [ I32 ] } };
    { super = None; sfinal = true; comp = CFunc { params = [ I32 ]; results = [ vref ty_val ] } };
    { super = None; sfinal = true;
      comp = CFunc { params = [ vref ty_val; I32; I32 ]; results = [] } };
  ]

(* Field positions (field 0 is always the tag). *)
let p_a = 1 (* $Pair.left, $Lrec.label, $Clos.fn, $Wrap.value, $I32Box.n, $Str.bytes *)
let p_b = 2 (* $Pair.right, $Lrec.value, $Clos.env *)

(* ---------------- fixed function indices ----------------

   The runtime, accessors and constructors occupy the first slots so the
   compiler can call them by constant; lifted λE functions follow. The
   constructors exist for the host: JavaScript cannot build GC structs, and
   host capabilities (readfile, load) must hand values back in. *)

let fn_strcat = 0
let fn_streq = 1
let fn_tag = 2
let fn_num = 3
let fn_str_len = 4
let fn_str_byte = 5
let fn_pair_a = 6
let fn_pair_b = 7
let fn_lrec_name_len = 8
let fn_lrec_name_byte = 9
let fn_lrec_val = 10
let fn_wrap_val = 11
let fn_unitval = 12
let fn_new_str = 13
let fn_set_str_byte = 14
let fn_inl = 15
let fn_inr = 16
let fn_lrec = 17
let fn_main = 18
let runtime_count = 19

let exports =
  [
    ("main", fn_main); ("tag", fn_tag); ("num", fn_num);
    ("strLen", fn_str_len); ("strByte", fn_str_byte);
    ("pairA", fn_pair_a); ("pairB", fn_pair_b);
    ("lrecNameLen", fn_lrec_name_len); ("lrecNameByte", fn_lrec_name_byte);
    ("lrecVal", fn_lrec_val); ("wrapVal", fn_wrap_val);
    ("unitval", fn_unitval); ("newStr", fn_new_str);
    ("setStrByte", fn_set_str_byte);
    ("inl", fn_inl); ("inr", fn_inr); ("lrec", fn_lrec);
  ]

(* Globals. *)
let gl_unit = 0

(* Every string literal and label name lives in this one passive segment. *)
let strings_data = 0
