(* λE -> WebAssembly-GC.

   λE has no variables: `Query` *is* the environment, and the environment is an
   ordinary value. So there is no closure-conversion pass here — the calculus
   arrives pre-converted. Two things follow, and they shape everything below.

   1. A function compiles to a lifted wasm function `(self, arg) -> result`
      whose body rebuilds its own environment out of `self`. A `Lam` body knows
      statically that it is a `Lam` body, so `App` never has to ask what kind
      of closure it received: read the funcref out of the $Clos struct and
      `call_ref`. No table, no slots, no indirection.

   2. `Proj` and `Rproj` are searches in the interpreter, but the program is
      typed and a merge value's shape mirrors its type's shape. `Check.tlookup`
      and the record path below therefore settle every access at compile time,
      so both compile to a fixed chain of casts and struct.gets — no spine
      walk, no label comparison at runtime.

   Values are GC structs subtyping $Val (see Abi), tagged so the host can
   render a result without being told its type. The engine's collector owns
   the heap; the module has no linear memory at all. λE types are erased —
   they direct compilation and then vanish. *)

module C = Core_lambdae.Ast
module Check = Core_lambdae.Check
open Ir
open Abi

exception Error of string

let err fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

(* ---------------- static data ---------------- *)

type state = {
  strings : Buffer.t; (* the one passive data segment *)
  mutable string_offs : (string * (int * int)) list; (* bytes -> (off, len) *)
  mutable lifted : func list; (* in function-index order *)
}

let new_state () = { strings = Buffer.create 64; string_offs = []; lifted = [] }

let string_slice st s =
  match List.assoc_opt s st.string_offs with
  | Some ol -> ol
  | None ->
    let off = Buffer.length st.strings in
    Buffer.add_string st.strings s;
    let ol = (off, String.length s) in
    st.string_offs <- (s, ol) :: st.string_offs;
    ol

(* ---------------- per-function locals ----------------

   Every local the compiler introduces holds a value, so they are uniformly
   (ref null $Val) — nullable, hence defaultable, hence free of the
   definite-assignment rules non-null locals carry. *)

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
      else Option.map (fun (p, t) -> (Right :: p, t)) (rlookup_path a2 l)
    else Option.map (fun (p, t) -> (Left :: p, t)) (rlookup_path a1 l)
  | _ -> None

let step_instrs = function
  | Left -> [ RefCast ty_pair; StructGet (ty_pair, p_a) ]
  | Right -> [ RefCast ty_pair; StructGet (ty_pair, p_b) ]

(* unbox the i32 payload of an Int or Bool *)
let unbox = [ RefCast ty_i32box; StructGet (ty_i32box, p_a) ]

(* ---------------- the compilation scheme ----------------

   `comp` leaves exactly one (ref null $Val) on the stack and returns the λE
   type of what it left there, so the caller can resolve its own static
   accesses. It follows `Check.infer` rule for rule. *)

let rec comp st fb ~env ~ctx (e : C.exp) : instr list * C.typ =
  match e with
  | C.Query -> ([ Local_get env ], ctx)
  | C.Unit -> ([ Global_get gl_unit ], C.TTop)
  | C.Lit (C.Int n) -> ([ Const tag_int; Const n; StructNew ty_i32box ], C.TInt)
  | C.Lit (C.Bool b) ->
    ([ Const tag_bool; Const (if b then 1 else 0); StructNew ty_i32box ], C.TBool)
  | C.Lit (C.String s) ->
    let off, len = string_slice st s in
    ( [ Const tag_str; Const off; Const len;
        ArrayNewData (ty_bytes, strings_data); StructNew ty_str ],
      C.TString )
  | C.Proj (e1, n) ->
    let is1, t1 = comp st fb ~env ~ctx e1 in
    (* lookup (Mrg (l, r)) 0 = r, and n > 0 descends left first *)
    let rec walk k =
      if k = 0 then step_instrs Right else step_instrs Left @ walk (k - 1)
    in
    (is1 @ walk n, Check.tlookup t1 n)
  | C.Rproj (e1, l) -> (
    let is1, t1 = comp st fb ~env ~ctx e1 in
    match rlookup_path t1 l with
    | None -> err "no unambiguous field labelled %s" l
    | Some (path, t) ->
      (* the route lands on the $Lrec; its payload is the field *)
      ( is1
        @ List.concat_map step_instrs path
        @ [ RefCast ty_lrec; StructGet (ty_lrec, p_b) ],
        t ))
  | C.Lrec (l, e1) ->
    (* the label name rides in the value, so separately compiled modules agree
       on rendering without any shared table *)
    let off, len = string_slice st l in
    let is1, t1 = comp st fb ~env ~ctx e1 in
    ( [ Const tag_lrec; Const off; Const len;
        ArrayNewData (ty_bytes, strings_data) ]
      @ is1 @ [ StructNew ty_lrec ],
      C.TRcd (l, t1) )
  | C.Mrg (e1, e2) ->
    (* the right operand is checked, and evaluated, under ctx & typeof e1 *)
    let is1, a = comp st fb ~env ~ctx e1 in
    let v1 = fresh fb in
    let env2 = fresh fb in
    let is2, b = comp st fb ~env:env2 ~ctx:(C.TAnd (ctx, a)) e2 in
    ( is1
      @ [ Local_set v1;
          Const tag_mrg; Local_get env; Local_get v1; StructNew ty_pair;
          Local_set env2;
          Const tag_mrg; Local_get v1 ]
      @ is2 @ [ StructNew ty_pair ],
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
      (* self, then argument, then the funcref call_ref pops last *)
      ( is1 @ [ Local_tee f ] @ is2
        @ [ Local_get f; RefCast ty_clos; StructGet (ty_clos, p_a);
            CallRef ty_fn ],
        b )
    | _ -> err "application of a non-function")
  | C.Lam (a, body) ->
    let b, fi = lift st ~kind:`Lam ~ctx ~a ~b:None body in
    ([ Const tag_clos; RefFunc fi; Local_get env; StructNew ty_clos ],
      C.TArr (a, b))
  | C.Flam (a, b, body) ->
    let b', fi = lift st ~kind:`Flam ~ctx ~a ~b:(Some b) body in
    if b' <> b then err "recursive function body type mismatch";
    ([ Const tag_fclos; RefFunc fi; Local_get env; StructNew ty_clos ],
      C.TArr (a, b))
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
    (isc @ unbox @ [ If ([ Ref ty_val ], ist, isf) ], tt)
  | C.Inl (b, e1) ->
    let is1, a = comp st fb ~env ~ctx e1 in
    ([ Const tag_inl ] @ is1 @ [ StructNew ty_wrap ], C.TOr (a, b))
  | C.Inr (a, e1) ->
    let is1, b = comp st fb ~env ~ctx e1 in
    ([ Const tag_inr ] @ is1 @ [ StructNew ty_wrap ], C.TOr (a, b))
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
        [ Const tag_mrg; Local_get env;
          Local_get v; RefCast ty_wrap; StructGet (ty_wrap, p_a);
          StructNew ty_pair; Local_set target ]
      in
      ( is1
        @ [ Local_set v; Local_get v; StructGet (ty_val, 0); Const tag_inl; Eq ]
        @ [ If ([ Ref ty_val ], bind envl @ isl, bind envr @ isr) ],
        tl )
    | _ -> err "case scrutinee is not a union")
  | C.Fold (t, e1) ->
    let is1, a = comp st fb ~env ~ctx e1 in
    if a <> Check.unfold_mu t then err "fold body does not match unrolled type";
    ([ Const tag_fold ] @ is1 @ [ StructNew ty_wrap ], C.TMu t)
  | C.Unfold e1 -> (
    let is1, t1 = comp st fb ~env ~ctx e1 in
    match t1 with
    | C.TMu t ->
      (is1 @ [ RefCast ty_wrap; StructGet (ty_wrap, p_a) ], Check.unfold_mu t)
    | _ -> err "unfold applied to a non-recursive type")
  | C.Clos _ | C.Fclos _ ->
    err "closure values cannot appear in a compiled program"

and binop op t1 is1 is2 =
  (* unbox both operands, apply `i`, and rebox the i32 result under `tag` *)
  let ibox tag i =
    (Const tag :: is1) @ unbox @ is2 @ unbox @ [ i; StructNew ty_i32box ]
  in
  match (op : C.binop) with
  | C.Add -> ibox tag_int Add
  | C.Sub -> ibox tag_int Sub
  | C.Mul -> ibox tag_int Mul
  | C.Div -> ibox tag_int Div_s
  | C.Mod -> ibox tag_int Rem_s
  | C.Lt -> ibox tag_bool Lt_s
  | C.Le -> ibox tag_bool Le_s
  | C.Gt -> ibox tag_bool Gt_s
  | C.Ge -> ibox tag_bool Ge_s
  | C.Cat -> is1 @ is2 @ [ Call fn_strcat ]
  | C.Eq | C.Ne ->
    let negate = if op = C.Ne then [ Eqz ] else [] in
    if t1 = C.TString then
      [ Const tag_bool ] @ is1 @ is2
      @ [ Call fn_streq ] @ negate @ [ StructNew ty_i32box ]
    else
      (* i32.ne exists, so integer Ne needs no extra negation *)
      [ Const tag_bool ] @ is1 @ unbox @ is2 @ unbox
      @ [ (if op = C.Eq then Eq else Ne); StructNew ty_i32box ]

(* Lift a function body into its own wasm function. The body rebuilds the
   environment the interpreter would have handed it: `Mrg (cenv, arg)` for a
   lambda, `Mrg (Mrg (cenv, self), arg)` for a fixpoint, so the argument is
   ?.0 and the function itself is ?.1. `self` as a value *is* the closure
   struct, so the fixpoint case just pushes param 0 back. *)
and lift st ~kind ~ctx ~a ~b body =
  let fb = { nparams = 2; nlocals = 0 } in
  let envl = fresh fb in
  let cenv = [ Local_get 0; RefCast ty_clos; StructGet (ty_clos, p_b) ] in
  let prologue =
    match kind with
    | `Lam ->
      [ Const tag_mrg ] @ cenv @ [ Local_get 1; StructNew ty_pair; Local_set envl ]
    | `Flam ->
      [ Const tag_mrg; Const tag_mrg ] @ cenv
      @ [ Local_get 0; StructNew ty_pair;
          Local_get 1; StructNew ty_pair; Local_set envl ]
  in
  let inner_ctx =
    match kind with
    | `Lam -> C.TAnd (ctx, a)
    | `Flam -> C.TAnd (C.TAnd (ctx, C.TArr (a, Option.get b)), a)
  in
  (* Reserve the function index *before* compiling: the body may lift further
     functions of its own, so the index cannot be read off the list length
     afterwards. *)
  let placeholder = { fn_name = "lifted"; fn_type = ty_fn; fn_locals = []; fn_body = [] } in
  st.lifted <- st.lifted @ [ placeholder ];
  let slot = List.length st.lifted - 1 in
  let fi = runtime_count + slot in
  let is, t = comp st fb ~env:envl ~ctx:inner_ctx body in
  let f =
    {
      fn_name = Printf.sprintf "lifted%d" slot;
      fn_type = ty_fn;
      fn_locals = List.init fb.nlocals (fun _ -> Ref ty_val);
      fn_body = prologue @ is;
    }
  in
  st.lifted <- List.mapi (fun i x -> if i = slot then f else x) st.lifted;
  (t, fi)

(* ---------------- module assembly ---------------- *)

let word n =
  let b = Bytes.create 4 in
  Bytes.set_int32_le b 0 (Int32.of_int n);
  Bytes.to_string b

let assemble st ~imports ~customs (main : func) : Ir.modul =
  {
    m_types = typedefs;
    m_imports = imports;
    m_funcs = Runtime.funcs @ [ main ] @ st.lifted;
    m_globals =
      [ { gl_name = "unit"; gl_type = Ref ty_val; gl_mut = false;
          gl_init = [ Const tag_unit; StructNew ty_val ] } ];
    m_exports = List.map (fun (n, i) -> { ex_name = n; ex_func = i }) exports;
    m_declared = List.mapi (fun i _ -> runtime_count + i) st.lifted;
    m_datas =
      (if Buffer.length st.strings = 0 then [] else [ Buffer.contents st.strings ]);
    m_customs = customs;
  }

(* Compile `e` as the body of `main`. `prologue env` seeds the environment
   local before the body runs. *)
let build ~imports ~customs ~prologue ~ctx (e : C.exp) : Ir.modul =
  let st = new_state () in
  let fb = { nparams = 0; nlocals = 0 } in
  let env = fresh fb in
  let body, _ = comp st fb ~env ~ctx e in
  let main =
    {
      fn_name = "main";
      fn_type = ty_0v;
      fn_locals = List.init fb.nlocals (fun _ -> Ref ty_val);
      fn_body = prologue env @ body;
    }
  in
  assemble st ~imports ~customs main

(* The top-level environment is Unit — the same environment
   `Eval.eval C.Unit` starts from. *)
let program (e : C.exp) : Ir.modul =
  build ~imports:[] ~customs:[] ~ctx:C.TTop
    ~prologue:(fun env -> [ Global_get gl_unit; Local_set env ])
    e

(* ---------------- the link module ----------------

   Linking at the wasm level is this compiler applied to the linkers' shared
   composition term, with the units installed through imports instead of
   spliced in: main's prologue calls each imported `u<k>.main` once and merges
   the values into the environment, so `Query` *is* the loaded units and every
   unit occurrence in the composition is an ordinary `Proj (Query, i)`. The
   expected unit names ride in an `sce.units` custom section so the host can
   check the instantiation order. *)

let link_module ~(names : string list) ~(unit_types : C.typ list)
    (body : C.exp) : Ir.modul =
  let prologue env =
    [ Global_get gl_unit; Local_set env ]
    @ List.concat
        (List.mapi
           (fun k _ ->
             [ Const tag_mrg; Local_get env; CallImport k;
               StructNew ty_pair; Local_set env ])
           names)
  in
  let manifest =
    word (List.length names)
    ^ String.concat "" (List.map (fun n -> word (String.length n) ^ n) names)
  in
  build
    ~imports:(List.mapi (fun k _ -> (Printf.sprintf "u%d" k, "main", ty_0v)) names)
    ~customs:[ ("sce.units", manifest) ]
    ~ctx:(List.fold_left (fun acc t -> C.TAnd (acc, t)) C.TTop unit_types)
    ~prologue body

let to_binary (e : C.exp) : string = Emit.modul (program e)
let to_wat (e : C.exp) : string = Wat.modul (program e)
let link_binary ~names ~unit_types body = Emit.modul (link_module ~names ~unit_types body)
let link_wat ~names ~unit_types body = Wat.modul (link_module ~names ~unit_types body)