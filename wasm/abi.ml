(* The contract between the compiler, the emitted runtime, and the host.

   Every λE value is an i32 pointer to a tagged cell in linear memory. Cells are
   self-describing so `run.js` can render a result without being told its type,
   which is what lets the wasm output be diffed against the OCaml interpreter. *)

open Ir

(* ---------------- cell tags ----------------

   one-word payload:  [tag][a]
   two-word payload:  [tag][a][b] *)

let tag_int = 0 (* [0][n]                 *)
let tag_bool = 1 (* [1][0|1]               *)
let tag_str = 2 (* [2][bytes ptr][length] *)
let tag_unit = 3 (* [3]                    *)
let tag_mrg = 4 (* [4][left][right]       *)
let tag_lrec = 5 (* [5][label id][value]   *)
let tag_clos = 6 (* [6][table slot][env]   *)
let tag_fclos = 7 (* [7][table slot][env]   *)
let tag_inl = 8 (* [8][value]             *)
let tag_inr = 9 (* [9][value]             *)
let tag_fold = 10 (* [10][value]            *)

let f_tag = 0
let f_a = 4
let f_b = 8

(* ---------------- memory map ---------------- *)

let unit_addr = 4 (* the one and only Unit cell *)
let data_base = 8 (* literals, string bytes, label names, then the label table *)

(* ---------------- fixed indices ----------------

   Runtime helpers occupy the first function slots so the compiler can call
   them by constant; lifted λE functions follow, and a lifted function's table
   slot is its position among them. *)

let fn_alloc = 0
let fn_box1 = 1
let fn_box2 = 2
let fn_mrg = 3
let fn_strcat = 4
let fn_streq = 5
let fn_main = 6
let runtime_count = 7

let ty_1 = 0 (* (i32) -> i32           *)
let ty_2 = 1 (* (i32, i32) -> i32      *)
let ty_3 = 2 (* (i32, i32, i32) -> i32 *)
let ty_0 = 3 (* () -> i32              *)

let types =
  [
    { params = [ I32 ]; results = [ I32 ] };
    { params = [ I32; I32 ]; results = [ I32 ] };
    { params = [ I32; I32; I32 ]; results = [ I32 ] };
    { params = []; results = [ I32 ] };
  ]

(* Global indices. *)
let gl_hp = 0 (* bump pointer, mutable   *)
let gl_labels = 1 (* address of the label table *)

let page_size = 65536
