(* The prelude every emitted module carries.

   With GC structs, allocation and cell construction are single instructions,
   so the runtime shrinks to the two string primitives that need a loop — plus
   the accessor exports that let run.js walk a result value, since JavaScript
   cannot look inside GC structs itself. *)

open Ir
open Abi

let fn name typ locals body =
  { fn_name = name; fn_type = typ; fn_locals = locals; fn_body = body }

(* the bytes array of a $Str value *)
let str_bytes local = [ Local_get local; RefCast ty_str; StructGet (ty_str, p_a) ]

(* strcat (a, b) -> $Str *)
let strcat =
  let ba = 2 and bb = 3 and la = 4 and lb = 5 and dst = 6 in
  fn "strcat" ty_fn [ Ref ty_bytes; Ref ty_bytes; I32; I32; Ref ty_bytes ]
    (str_bytes 0 @ [ Local_set ba ]
    @ str_bytes 1 @ [ Local_set bb ]
    @ [
        Local_get ba; ArrayLen; Local_set la;
        Local_get bb; ArrayLen; Local_set lb;
        Local_get la; Local_get lb; Add; ArrayNewDefault ty_bytes; Local_set dst;
        (* array.copy: dst, dst offset, src, src offset, length *)
        Local_get dst; Const 0; Local_get ba; Const 0; Local_get la;
        ArrayCopy (ty_bytes, ty_bytes);
        Local_get dst; Local_get la; Local_get bb; Const 0; Local_get lb;
        ArrayCopy (ty_bytes, ty_bytes);
        Const tag_str; Local_get dst; StructNew ty_str;
      ])

(* streq (a, b) -> 0 | 1 *)
let streq =
  let ba = 2 and bb = 3 and la = 4 and i = 5 in
  fn "streq" ty_vv2i [ Ref ty_bytes; Ref ty_bytes; I32; I32 ]
    (str_bytes 0 @ [ Local_set ba ]
    @ str_bytes 1 @ [ Local_set bb ]
    @ [
        Local_get ba; ArrayLen; Local_set la;
        Local_get la; Local_get bb; ArrayLen; Ne;
        If
          ( [ I32 ],
            [ Const 0 ],
            [
              Const 0; Local_set i;
              Block
                ( [ I32 ],
                  [
                    Loop
                      ( [],
                        [
                          Local_get i; Local_get la; Lt_s;
                          If
                            ( [],
                              [
                                Local_get ba; Local_get i; ArrayGetU ty_bytes;
                                Local_get bb; Local_get i; ArrayGetU ty_bytes;
                                Ne;
                                (* mismatch: leave the block with 0 *)
                                If ([], [ Const 0; Br 3 ], []);
                                Local_get i; Const 1; Add; Local_set i;
                                Br 1;
                              ],
                              [] );
                        ] );
                    Const 1;
                  ] );
            ] );
      ])

(* ---------------- host accessors ---------------- *)

let getter name typ cast field =
  fn name typ [] [ Local_get 0; RefCast cast; StructGet (cast, field) ]

let tag_f = fn "tag" ty_v2i [] [ Local_get 0; StructGet (ty_val, 0) ]
let num_f = getter "num" ty_v2i ty_i32box p_a
let str_len = fn "strLen" ty_v2i [] (str_bytes 0 @ [ ArrayLen ])
let str_byte =
  fn "strByte" ty_vi2i [] (str_bytes 0 @ [ Local_get 1; ArrayGetU ty_bytes ])
let pair_a = getter "pairA" ty_v2v ty_pair p_a
let pair_b = getter "pairB" ty_v2v ty_pair p_b

(* the label name of an $Lrec, carried in the value itself so results from
   separately compiled modules render without shared metadata *)
let lrec_name local = [ Local_get local; RefCast ty_lrec; StructGet (ty_lrec, p_a) ]
let lrec_name_len = fn "lrecNameLen" ty_v2i [] (lrec_name 0 @ [ ArrayLen ])
let lrec_name_byte =
  fn "lrecNameByte" ty_vi2i [] (lrec_name 0 @ [ Local_get 1; ArrayGetU ty_bytes ])
let lrec_val = getter "lrecVal" ty_v2v ty_lrec p_b
let wrap_val = getter "wrapVal" ty_v2v ty_wrap p_a

(* In the order Abi's fixed indices promise. *)
let funcs =
  [ strcat; streq; tag_f; num_f; str_len; str_byte;
    pair_a; pair_b; lrec_name_len; lrec_name_byte; lrec_val; wrap_val ]
