(* λE -> WebAssembly.

   λE has no variables: `Query` *is* the environment, and the environment is an
   ordinary value. So there is no closure-conversion pass here — the calculus
   arrives pre-converted. Two things follow, and they shape everything below.

   1. A function compiles to a lifted wasm function `(self, arg) -> result`
      whose body rebuilds its own environment out of `self`. A `Lam` body knows
      statically that it is a `Lam` body, so `App` never has to ask what kind
      of closure it received: load the table slot and `call_indirect`.

   2. `Proj` and `Rproj` are searches in the interpreter, but the program is
      typed and a merge value's shape mirrors its type's shape. `Check.tlookup`
      and the record path below therefore settle every access at compile time,
      so both compile to a fixed chain of loads — no spine walk, no label
      comparison at runtime.

   Values are boxed cells in linear memory, tagged so the host can render a
   result without being told its type. Allocation is a bump pointer; there is
   no GC. *)

module C = Core_lambdae.Ast
module Check = Core_lambdae.Check
open Ir
open Abi

exception Error of string

let err fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

(* ---------------- static data ---------------- *)

type state = {
  data : Buffer.t; (* static image, starting at data_base *)
  mutable ints : (int * int) list; (* literal -> address, memoized *)
  mutable bools : (bool * int) list;
  mutable strings : (string * int) list;
  mutable labels : (string * int) list; (* label -> id *)
  mutable label_bytes : (int * int) list; (* id -> (address, length) *)
  mutable lifted : func list; (* in table-slot order *)
}

let new_state () =
  {
    data = Buffer.create 256;
    ints = [];
    bools = [];
    strings = [];
    labels = [];
    label_bytes = [];
    lifted = [];
  }

let word n =
  let b = Bytes.create 4 in
  Bytes.set_uint8 b 0 (n land 0xff);
  Bytes.set_uint8 b 1 ((n asr 8) land 0xff);
  Bytes.set_uint8 b 2 ((n asr 16) land 0xff);
  Bytes.set_uint8 b 3 ((n asr 24) land 0xff);
  Bytes.to_string b

let next_addr st = data_base + Buffer.length st.data

(* Cells are read with i32.load, so everything static stays word-aligned. *)
let align st =
  while (next_addr st) land 3 <> 0 do
    Buffer.add_char st.data '\000'
  done

let put st bytes =
  align st;
  let addr = next_addr st in
  Buffer.add_string st.data bytes;
  addr

(* Every literal in the program is known up front, so literals are static cells
   and compile to a constant address rather than an allocation. *)
let lit_int st n =
  match List.assoc_opt n st.ints with
  | Some a -> a
  | None ->
    let a = put st (word tag_int ^ word n) in
    st.ints <- (n, a) :: st.ints;
    a

let lit_bool st b =
  match List.assoc_opt b st.bools with
  | Some a -> a
  | None ->
    let a = put st (word tag_bool ^ word (if b then 1 else 0)) in
    st.bools <- (b, a) :: st.bools;
    a

let lit_string st s =
  match List.assoc_opt s st.strings with
  | Some a -> a
  | None ->
    let bytes = put st s in
    let a = put st (word tag_str ^ word bytes ^ word (String.length s)) in
    st.strings <- (s, a) :: st.strings;
    a

(* Labels are interned; the cell stores an id, and the host maps ids to names
   through the table emitted at the end of the static image. *)
let label_id st l =
  match List.assoc_opt l st.labels with
  | Some i -> i
  | None ->
    let id = List.length st.labels in
    let addr = put st l in
    st.labels <- st.labels @ [ (l, id) ];
    st.label_bytes <- st.label_bytes @ [ (addr, String.length l) ];
    id

(* ---------------- per-function local allocation ---------------- *)

type fbuilder = { nparams : int; mutable nlocals : int }

let fresh fb =
  let i = fb.nparams + fb.nlocals in
  fb.nlocals <- fb.nlocals + 1;
  i

(* ---------------- static access paths ----------------

   `Rproj` needs the *route* to a label, not just its type, so this mirrors
   `Check.rlookup_typ_opt` while recording which side it descended into.
   Ambiguity is rejected there and here alike. *)

type step = Left | Right

let rec rlookup_path (a : C.typ) (l : string) : (step list * C.typ) option =
  match a with
  | C.TRcd (l', t) when String.equal l l' -> Some ([], t)
  | C.TAnd (a1, a2) ->
    if Check.lin l a2 then
      if Check.lin l a1 then None
      else
        Option.map (fun (p, t) -> (Right :: p, t)) (rlookup_path a2 l)
    else Option.map (fun (p, t) -> (Left :: p, t)) (rlookup_path a1 l)
  | _ -> None

let step_instr = function
  | Left -> Load { offset = f_a }
  | Right -> Load { offset = f_b }

(* ---------------- the compilation scheme ----------------

   `comp` leaves exactly one i32 — a pointer to the result cell — on the stack,
   and returns the λE type of what it left there so the caller can resolve its
   own static accesses. It follows `Check.infer` rule for rule. *)

let rec comp st fb ~env ~ctx (e : C.exp) : instr list * C.typ =
  match e with
  | C.Query -> ([ Local_get env ], ctx)
  | C.Unit -> ([ Const unit_addr ], C.TTop)
  | C.Lit (C.Int n) -> ([ Const (lit_int st n) ], C.TInt)
  | C.Lit (C.Bool b) -> ([ Const (lit_bool st b) ], C.TBool)
  | C.Lit (C.String s) -> ([ Const (lit_string st s) ], C.TString)
  | C.Proj (e1, n) ->
    let is1, t1 = comp st fb ~env ~ctx e1 in
    (* lookup (Mrg (l, r)) 0 = r, and n > 0 descends left first *)
    let rec walk k = if k = 0 then [ Load { offset = f_b } ] else Load { offset = f_a } :: walk (k - 1) in
    (is1 @ walk n, Check.tlookup t1 n)
  | C.Rproj (e1, l) -> (
    let is1, t1 = comp st fb ~env ~ctx e1 in
    match rlookup_path t1 l with
    | None -> err "no unambiguous field labelled %s" l
    | Some (path, t) ->
      (* the route lands on the Lrec cell; its payload is the field *)
      (is1 @ List.map step_instr path @ [ Load { offset = f_b } ], t))
  | C.Lrec (l, e1) ->
    let id = label_id st l in
    let is1, t1 = comp st fb ~env ~ctx e1 in
    ([ Const tag_lrec; Const id ] @ is1 @ [ Call fn_box2 ], C.TRcd (l, t1))
  | C.Mrg (e1, e2) ->
    (* the right operand is checked, and evaluated, under ctx & typeof e1 *)
    let is1, a = comp st fb ~env ~ctx e1 in
    let v1 = fresh fb in
    let env2 = fresh fb in
    let is2, b = comp st fb ~env:env2 ~ctx:(C.TAnd (ctx, a)) e2 in
    ( is1
      @ [ Local_set v1; Local_get env; Local_get v1; Call fn_mrg; Local_set env2 ]
      @ [ Local_get v1 ] @ is2 @ [ Call fn_mrg ],
      C.TAnd (a, b) )
  | C.Box (e1, e2) ->
    let is1, ctx' = comp st fb ~env ~ctx e1 in
    let env' = fresh fb in
    let is2, t = comp st fb ~env:env' ~ctx:ctx' e2 in
    (is1 @ [ Local_set env' ] @ is2, t)
  | C.App (e1, e2) -> (
    let is1, t1 = comp st fb ~env ~ctx e1 in
    match t1 with
    | C.TArr (a, b) ->
      let is2, a' = comp st fb ~env ~ctx e2 in
      if a' <> a then err "argument type mismatch";
      let f = fresh fb in
      (* self, then argument, then the table slot call_indirect pops last *)
      ( is1 @ [ Local_set f; Local_get f ] @ is2
        @ [ Local_get f; Load { offset = f_a }; Call_indirect ty_2 ],
        b )
    | _ -> err "application of a non-function")
  | C.Lam (a, body) ->
    let b, slot = lift st ~kind:`Lam ~ctx ~a ~b:None body in
    ([ Const tag_clos; Const slot; Local_get env; Call fn_box2 ], C.TArr (a, b))
  | C.Flam (a, b, body) ->
    let b', slot = lift st ~kind:`Flam ~ctx ~a ~b:(Some b) body in
    if b' <> b then err "recursive function body type mismatch";
    ([ Const tag_fclos; Const slot; Local_get env; Call fn_box2 ], C.TArr (a, b))
  | C.Binop (op, e1, e2) ->
    let is1, t1 = comp st fb ~env ~ctx e1 in
    let is2, t2 = comp st fb ~env ~ctx e2 in
    let result = Check.type_of_binop op t1 t2 in
    (binop op t1 is1 is2, result)
  | C.If (c, t, f) ->
    let isc, tc = comp st fb ~env ~ctx c in
    if tc <> C.TBool then err "if condition is not a boolean";
    let ist, tt = comp st fb ~env ~ctx t in
    let isf, tf = comp st fb ~env ~ctx f in
    if tt <> tf then err "if branches have different types";
    (isc @ [ Load { offset = f_a }; If ([ I32 ], ist, isf) ], tt)
  | C.Inl (b, e1) ->
    let is1, a = comp st fb ~env ~ctx e1 in
    ([ Const tag_inl ] @ is1 @ [ Call fn_box1 ], C.TOr (a, b))
  | C.Inr (a, e1) ->
    let is1, b = comp st fb ~env ~ctx e1 in
    ([ Const tag_inr ] @ is1 @ [ Call fn_box1 ], C.TOr (a, b))
  | C.Case (e1, el, er) -> (
    let is1, t1 = comp st fb ~env ~ctx e1 in
    match t1 with
    | C.TOr (a, b) ->
      let v = fresh fb in
      let envl = fresh fb in
      let envr = fresh fb in
      let isl, tl = comp st fb ~env:envl ~ctx:(C.TAnd (ctx, a)) el in
      let isr, tr = comp st fb ~env:envr ~ctx:(C.TAnd (ctx, b)) er in
      if tl <> tr then err "case branches have different types";
      let bind target =
        [ Local_get env; Local_get v; Load { offset = f_a }; Call fn_mrg; Local_set target ]
      in
      ( is1
        @ [ Local_set v; Local_get v; Load { offset = f_tag }; Const tag_inl; Eq ]
        @ [ If ([ I32 ], bind envl @ isl, bind envr @ isr) ],
        tl )
    | _ -> err "case scrutinee is not a union")
  | C.Fold (t, e1) ->
    let is1, a = comp st fb ~env ~ctx e1 in
    if a <> Check.unfold_mu t then err "fold body does not match unrolled type";
    ([ Const tag_fold ] @ is1 @ [ Call fn_box1 ], C.TMu t)
  | C.Unfold e1 -> (
    let is1, t1 = comp st fb ~env ~ctx e1 in
    match t1 with
    | C.TMu t -> (is1 @ [ Load { offset = f_a } ], Check.unfold_mu t)
    | _ -> err "unfold applied to a non-recursive type")
  | C.Clos _ | C.Fclos _ ->
    err "closure values cannot appear in a compiled program"

and binop op t1 is1 is2 =
  let unbox is = is @ [ Load { offset = f_a } ] in
  let arith i = [ Const tag_int ] @ unbox is1 @ unbox is2 @ [ i; Call fn_box1 ] in
  let compare i = [ Const tag_bool ] @ unbox is1 @ unbox is2 @ [ i; Call fn_box1 ] in
  match (op : C.binop) with
  | C.Add -> arith Add
  | C.Sub -> arith Sub
  | C.Mul -> arith Mul
  | C.Div -> arith Div_s
  | C.Mod -> arith Rem_s
  | C.Lt -> compare Lt_s
  | C.Le -> compare Le_s
  | C.Gt -> compare Gt_s
  | C.Ge -> compare Ge_s
  | C.Cat -> is1 @ is2 @ [ Call fn_strcat ]
  | C.Eq | C.Ne ->
    let negate = if op = C.Ne then [ Eqz ] else [] in
    if t1 = C.TString then
      [ Const tag_bool ] @ is1 @ is2 @ [ Call fn_streq ] @ negate @ [ Call fn_box1 ]
    else
      [ Const tag_bool ] @ unbox is1 @ unbox is2
      @ [ (if op = C.Eq then Eq else Ne) ]
      @ [ Call fn_box1 ]

(* Lift a function body into its own wasm function and record its table slot.
   The body rebuilds the environment the interpreter would have handed it:
   `Mrg (cenv, arg)` for a lambda, `Mrg (Mrg (cenv, self), arg)` for a
   fixpoint, so the argument is ?.0 and the function itself is ?.1. *)
and lift st ~kind ~ctx ~a ~b body =
  let fb = { nparams = 2; nlocals = 0 } in
  let envl = fresh fb in
  let prologue =
    match kind with
    | `Lam ->
      [ Local_get 0; Load { offset = f_b }; Local_get 1; Call fn_mrg; Local_set envl ]
    | `Flam ->
      [ Local_get 0; Load { offset = f_b }; Local_get 0; Call fn_mrg;
        Local_get 1; Call fn_mrg; Local_set envl ]
  in
  let inner_ctx =
    match kind with
    | `Lam -> C.TAnd (ctx, a)
    | `Flam -> C.TAnd (C.TAnd (ctx, C.TArr (a, Option.get b)), a)
  in
  (* Reserve the slot *before* compiling: the body may lift further functions
     of its own, so the slot cannot be read off the list length afterwards. *)
  let placeholder = { fn_name = "lifted"; fn_type = ty_2; fn_locals = []; fn_body = [] } in
  st.lifted <- st.lifted @ [ placeholder ];
  let slot = List.length st.lifted - 1 in
  let is, t = comp st fb ~env:envl ~ctx:inner_ctx body in
  let f =
    {
      fn_name = Printf.sprintf "lifted%d" slot;
      fn_type = ty_2;
      fn_locals = List.init fb.nlocals (fun _ -> I32);
      fn_body = prologue @ is;
    }
  in
  st.lifted <- List.mapi (fun i x -> if i = slot then f else x) st.lifted;
  (t, slot)

(* ---------------- module assembly ----------------

   The static image is laid out literals-first, then the label table, and the
   heap starts after it. Both globals are initialised from addresses that are
   only known once compilation has finished, which is why they are filled in
   here rather than up front. *)

let program (e : C.exp) : Ir.modul =
  let st = new_state () in
  let fb = { nparams = 0; nlocals = 0 } in
  (* local 0 of `main` holds the top-level environment, which is Unit — the
     same environment `Eval.eval C.Unit` starts from. *)
  let env = fresh fb in
  let body, _ = comp st fb ~env ~ctx:C.TTop e in
  let main =
    {
      fn_name = "main";
      fn_type = ty_0;
      fn_locals = List.init fb.nlocals (fun _ -> I32);
      fn_body = [ Const unit_addr; Local_set env ] @ body;
    }
  in
  (* The label table, so the host can turn the id inside an Lrec cell back into
     a field name: a count, then one (address, length) pair per label. *)
  let table =
    word (List.length st.label_bytes)
    ^ String.concat "" (List.map (fun (a, n) -> word a ^ word n) st.label_bytes)
  in
  let labels_addr = put st table in
  align st;
  let heap_base = next_addr st in
  let pages = max 1 ((heap_base + page_size - 1) / page_size) in
  {
    m_types = types;
    m_funcs = Runtime.funcs @ [ main ] @ st.lifted;
    m_table = List.length st.lifted;
    m_elems = List.mapi (fun i _ -> runtime_count + i) st.lifted;
    m_pages = pages;
    m_globals =
      [
        { gl_name = "hp"; gl_mut = true; gl_init = heap_base };
        { gl_name = "labels"; gl_mut = false; gl_init = labels_addr };
      ];
    m_exports =
      [
        { ex_name = "memory"; ex_desc = ExMemory 0 };
        { ex_name = "main"; ex_desc = ExFunc fn_main };
        { ex_name = "labels"; ex_desc = ExGlobal gl_labels };
      ];
    m_datas =
      [
        { da_offset = unit_addr; da_bytes = word tag_unit };
        { da_offset = data_base; da_bytes = Buffer.contents st.data };
      ];
  }

let to_binary (e : C.exp) : string = Emit.modul (program e)
let to_wat (e : C.exp) : string = Wat.modul (program e)
