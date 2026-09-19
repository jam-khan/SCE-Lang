open Ast

exception Error of string

module F = Frames.Make (struct
  type t = binder
end)


let index (frames : F.env) (x : binder) : int option =
  let rec go i ls =
    match ls with
    | [] -> None
    | y :: rest -> if String.equal x y then Some i else go (i + 1) rest
  in go 0 frames

let rec go (fr : F.env) (e : named) : nameless =
  let here e = go fr e in
  match e with
  | Var x -> (
    match index fr x with
    | Some i -> Proj (Query, i)
    | None -> raise (Error (Printf.sprintf "unresolved name '%s'" x)))
  | Query -> Query
  | Lit l -> Lit l
  | Unit -> Unit
  (* ---- binding forms: one entry per Frames rule ---- *)
  | Lam (x, a, body) -> Lam (x, a, go (F.lam x fr) body)
  | Letb (x, e1, e2) -> Letb (x, here e1, go (F.letb x fr) e2)
  | Mrg (x, e1, e2) -> Mrg (x, here e1, go (F.mrg x fr) e2)
  | Nmrg (e1, e2) -> Nmrg (here e1, go (F.nmrg anon fr) e2)
  | Openm (x, e1, e2) -> Openm (x, here e1, go (F.openm x fr) e2)
  | Case (e1, x, el, y, er) ->
    Case (here e1, x, go (F.case_branch x fr) el, y, go (F.case_branch y fr) er)
  | Flam (f, x, a, b, body) ->
    Flam (f, x, a, b, go (F.flam ~self:f ~arg:x fr) body)
  | Mfunctor (sb, x, a, body) ->
    let outer = match sb with Sandboxed -> F.sandbox fr | Open -> fr in
    Mfunctor (sb, x, a, go (F.lam x outer) body)
  | Mstruct body -> Mstruct (here body)
  | Box (e1, e2) -> Box (here e1, go (F.box fr) e2)
  (* ---- congruence ---- *)
  | Proj (e1, i) -> Proj (here e1, i)
  | App (e1, e2) -> App (here e1, here e2)
  | Mapp (e1, e2) -> Mapp (here e1, here e2)
  | Mlink (e1, e2) -> Mlink (here e1, here e2)
  | Mlinkn (e1, e2) -> Mlinkn (here e1, here e2)
  | Lrec (l, e1) -> Lrec (l, here e1)
  | Rproj (e1, l) -> Rproj (here e1, l)
  | Binop (op, e1, e2) -> Binop (op, here e1, here e2)
  | If (e1, e2, e3) -> If (here e1, here e2, here e3)
  | Inl (t, e1) -> Inl (t, here e1)
  | Inr (t, e1) -> Inr (t, here e1)
  | Fold (t, e1) -> Fold (t, here e1)
  | Unfold e1 -> Unfold (here e1)
  | Clos _ | Mclos _ | Fclos _ ->
    (* manufactured by the evaluator, never by the front end *)
    raise (Error "a closure cannot appear in a source term")

let resolve (e : named) : nameless = go F.empty e