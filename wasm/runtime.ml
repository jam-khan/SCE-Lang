(* The prelude every emitted module carries: allocation, cell construction, and
   the two string primitives that need a loop. *)

open Ir
open Abi

let fn name typ locals body = { fn_name = name; fn_type = typ; fn_locals = locals; fn_body = body }

(* alloc (size) -> ptr

   A bump pointer, rounded up to a word so every cell stays i32-aligned, then
   grow the memory a page at a time until the new top fits. There is no free
   and no GC. *)
let alloc =
  let size = 0 and p = 1 in
  fn "alloc" ty_1 [ I32 ]
    [
      (* size = (size + 3) & ~3 *)
      Local_get size; Const 3; Add; Const (-4); And; Local_set size;
      Global_get gl_hp; Local_set p;
      Global_get gl_hp; Local_get size; Add; Global_set gl_hp;
      Loop
        ( [],
          [
            Global_get gl_hp; Memory_size; Const page_size; Mul; Gt_s;
            If ([], [ Const 1; Memory_grow; Drop; Br 1 ], []);
          ] );
      Local_get p;
    ]

(* box1 (tag, a) -> ptr *)
let box1 =
  let tag = 0 and a = 1 and p = 2 in
  fn "box1" ty_2 [ I32 ]
    [
      Const 8; Call fn_alloc; Local_set p;
      Local_get p; Local_get tag; Store { offset = f_tag };
      Local_get p; Local_get a; Store { offset = f_a };
      Local_get p;
    ]

(* box2 (tag, a, b) -> ptr *)
let box2 =
  let tag = 0 and a = 1 and b = 2 and p = 3 in
  fn "box2" ty_3 [ I32 ]
    [
      Const 12; Call fn_alloc; Local_set p;
      Local_get p; Local_get tag; Store { offset = f_tag };
      Local_get p; Local_get a; Store { offset = f_a };
      Local_get p; Local_get b; Store { offset = f_b };
      Local_get p;
    ]

(* mrg (left, right) -> ptr

   Its own function purely so the compiler can push operands in their natural
   order at every `Mrg`, of which there is one per binder. *)
let mrg =
  fn "mrg" ty_2 [] [ Const tag_mrg; Local_get 0; Local_get 1; Call fn_box2 ]

(* strcat (a, b) -> ptr — byte-by-byte, staying inside the 1.0 instruction set
   rather than reaching for bulk memory. *)
let strcat =
  let a = 0 and b = 1 and la = 2 and lb = 3 and dst = 4 and i = 5 in
  let copy ~src ~len ~base =
    [
      Const 0; Local_set i;
      Loop
        ( [],
          [
            Local_get i; Local_get len; Lt_s;
            If
              ( [],
                base
                @ [ Local_get i; Add ]
                @ [ Local_get src; Load { offset = f_a }; Local_get i; Add;
                    Load8_u { offset = 0 } ]
                @ [ Store8 { offset = 0 } ]
                @ [ Local_get i; Const 1; Add; Local_set i; Br 1 ],
                [] );
          ] );
    ]
  in
  fn "strcat" ty_2 [ I32; I32; I32; I32 ]
    (
      [
        Local_get a; Load { offset = f_b }; Local_set la;
        Local_get b; Load { offset = f_b }; Local_set lb;
        Local_get la; Local_get lb; Add; Call fn_alloc; Local_set dst;
      ]
      @ copy ~src:a ~len:la ~base:[ Local_get dst ]
      @ copy ~src:b ~len:lb ~base:[ Local_get dst; Local_get la; Add ]
      @ [ Const tag_str; Local_get dst; Local_get la; Local_get lb; Add; Call fn_box2 ]
    )

(* streq (a, b) -> 0 | 1 *)
let streq =
  let a = 0 and b = 1 and la = 2 and i = 3 in
  fn "streq" ty_2 [ I32; I32 ]
    [
      Local_get a; Load { offset = f_b }; Local_set la;
      Local_get la; Local_get b; Load { offset = f_b }; Ne;
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
                              Local_get a; Load { offset = f_a }; Local_get i; Add;
                              Load8_u { offset = 0 };
                              Local_get b; Load { offset = f_a }; Local_get i; Add;
                              Load8_u { offset = 0 };
                              Ne;
                              (* branch out of the enclosing block with 0 *)
                              If ([], [ Const 0; Br 3 ], []);
                              Local_get i; Const 1; Add; Local_set i;
                              Br 1;
                            ],
                            [] );
                      ] );
                  Const 1;
                ] );
          ] );
    ]

let funcs = [ alloc; box1; box2; mrg; strcat; streq ]
