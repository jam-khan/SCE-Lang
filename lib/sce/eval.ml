(* Evaluation for λSCE. *)
open Ast

(* LookupV: index 0 is the *right-most* component of a merge. *)
let rec lookup (v : exp) (i : int) : exp =
  match v with
  | Mrg (v1, v2) | Nmrg (v1, v2) ->
    if i = 0 then v2 else lookup v1 (i - 1)
  | _ -> failwith ("Error: no component at index " ^ string_of_int i)

(* Sel with option response *)
let rec sel_opt (v : exp) (l : string) : exp option =
  match v with
  | Lrec (l', v') when String.equal l l' -> Some v'
  | Mrg (v1, v2) | Nmrg (v1, v2) ->
    (match sel_opt v2 l with
     | Some _ as r -> r
     | None -> sel_opt v1 l)
  | _ -> None

(* Sel: label `l` selection in `v` *)
let sel (v : exp) (l : string) : exp =
  match sel_opt v l with
  | Some v' -> v'
  | None -> failwith ("Error: no field labelled " ^ l)

(* SelPkg: build the record package for the import interface `d` out of `v`. *)
let rec selpkg (v : exp) (d : typ) : exp =
  match d with
  | TRcd (l, _) -> Lrec (l, sel v l)
  | TAnd (d', TRcd (l, _)) -> Mrg (selpkg v d', Lrec (l, sel v l))
  | _ -> failwith "Error: import interface must be a record or intersection of records."

(* Interpreter based on big-step semantics. *)
let rec eval (env : exp) (e : exp) : exp =
  match e with
  | Lit _ | Unit | Clos _ | Mclos _ | Fclos _ -> e
  | Query -> env
  | Lam (ty, body) -> Clos (env, ty, body)
  | Flam (tyA, tyB, body) -> Fclos (env, tyA, tyB, body)
  | Box (e1, e2) ->
    let env' = eval env e1 in
    eval env' e2
  | Mrg (e1, e2) ->
    let v1 = eval env e1 in
    Mrg (v1, eval (Mrg (env, v1)) e2)
  | Nmrg (e1, e2) ->
    let v1 = eval env e1 in
    Mrg (v1, eval env e2)
  | App (e1, e2) ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    begin match v1 with
      | Clos (cenv, _ty, body) -> eval (Mrg (cenv, v2)) body
      | Fclos (cenv, _tyA, _tyB, body) ->
        eval (Mrg (Mrg (cenv, v1), v2)) body
      | _ -> failwith "Error: Application (e1 e2) must have e1 as closure."
    end
  | Mapp (e1, e2) ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    begin match v1 with
      | Mclos (cenv, _ty, body) -> eval (Mrg (cenv, v2)) body
      | _ -> failwith "Error: Module application (e1 e2) must have e1 as module closure."
    end
  | Proj (e1, i) -> lookup (eval env e1) i
  | Lrec (l, e1) -> Lrec (l, eval env e1)
  | Rproj (e1, l) -> sel (eval env e1) l
  | Letb (e1, _ty, e2) ->
    let v1 = eval env e1 in
    eval (Mrg (env, v1)) e2
  | Openm (e1, e2) ->
    begin match eval env e1 with
      | Lrec (_l, v') -> eval (Mrg (env, v')) e2
      | _ -> failwith "Error: Open must have a labelled record as its subject."
    end
  | Mstruct (Sandboxed, body) -> eval Unit body
  | Mstruct (Open, body) -> eval env body
  | Mfunctor (Sandboxed, ty, body) -> Mclos (Unit, ty, body)
  | Mfunctor (Open, ty, body) -> Mclos (env, ty, body)
  | Mlink (e1, e2) ->
    let v1 = eval env e1 in
    begin match eval env e2 with
      | Mclos (cenv, TRcd (l, _), body) ->
        let vl = sel v1 l in
        Mrg (v1, eval (Mrg (cenv, Lrec (l, vl))) body)
      | _ -> failwith "Error: Link must have a module closure with a record import."
    end
  | Mlinkn (e1, e2) ->
    let v1 = eval env e1 in
    begin match eval env e2 with
      | Mclos (cenv, d, body) ->
        let pkg = selpkg v1 d in
        Mrg (v1, eval (Mrg (cenv, pkg)) body)
      | _ -> failwith "Error: N-ary link must have a module closure."
    end
  | Inl (ty, e1) -> Inl (ty, eval env e1)
  | Inr (ty, e1) -> Inr (ty, eval env e1)
  | Case (e1, el, er) ->
    begin match eval env e1 with
      | Inl (_, v) -> eval (Mrg (env, v)) el
      | Inr (_, v) -> eval (Mrg (env, v)) er
      | _ -> failwith "Error: Case analysis must evaluate to an injection."
    end
  | Fold (ty, e1) -> Fold (ty, eval env e1)
  | Unfold e1 ->
    begin match eval env e1 with
      | Fold (_, v) -> v
      | _ -> failwith "Error: Unfold applied to a non-fold value."
    end

(* Interpreter based on small-step semantics. *)
let rec step (env : exp) (e : exp) : exp =
  match e with
  | _ when is_value e -> e
  | Query -> env
  | Lam (ty, body) -> Clos (env, ty, body)
  | Flam (tyA, tyB, body) -> Fclos (env, tyA, tyB, body)
  | Mfunctor (Sandboxed, ty, body) -> Mclos (Unit, ty, body)
  | Mfunctor (Open, ty, body) -> Mclos (env, ty, body)
  | Box (e1, e2) ->
    if not (is_value e1) then Box (step env e1, e2)
    else if not (is_value e2) then Box (e1, step e1 e2)
    else e2
  | Mrg (e1, e2) ->
    if is_value e1 then Mrg (e1, step (Mrg (env, e1)) e2)
    else Mrg (step env e1, e2)
  | Nmrg (e1, e2) ->
    if not (is_value e1) then Nmrg (step env e1, e2)
    else if not (is_value e2) then Nmrg (e1, step env e2)
    else Mrg (e1, e2)
  | App (e1, e2) ->
    if not (is_value e1) then App (step env e1, e2)
    else if not (is_value e2) then App (e1, step env e2)
    else begin match e1 with
      | Clos (cenv, _ty, body) -> Box (Mrg (cenv, e2), body)
      | Fclos (cenv, _tyA, _tyB, body) -> Box (Mrg (Mrg (cenv, e1), e2), body)
      | _ -> failwith "Error: Application (e1 e2) must have e1 as closure."
    end
  | Mapp (e1, e2) ->
    if not (is_value e1) then Mapp (step env e1, e2)
    else if not (is_value e2) then Mapp (e1, step env e2)
    else begin match e1 with
      | Mclos (cenv, _ty, body) -> Box (Mrg (cenv, e2), body)
      | _ -> failwith "Error: Module application (e1 e2) must have e1 as module closure."
    end
  | Proj (e1, i) ->
    if is_value e1 then lookup e1 i else Proj (step env e1, i)
  | Lrec (l, e1) -> Lrec (l, step env e1)
  | Rproj (e1, l) ->
    if is_value e1 then sel e1 l else Rproj (step env e1, l)
  | Letb (e1, ty, e2) ->
    if is_value e1 then Box (Mrg (env, e1), e2)
    else Letb (step env e1, ty, e2)
  | Openm (e1, e2) ->
    if not (is_value e1) then Openm (step env e1, e2)
    else begin match e1 with
      | Lrec (_l, v') -> Box (Mrg (env, v'), e2)
      | _ -> failwith "Error: Open must have a labelled record as its subject."
    end
  | Mstruct (Sandboxed, e1) ->
    if is_value e1 then e1 else Mstruct (Sandboxed, step Unit e1)
  | Mstruct (Open, e1) ->
    if is_value e1 then e1 else Mstruct (Open, step env e1)
  | Mlink (e1, e2) ->
    if not (is_value e1) then Mlink (step env e1, e2)
    else if not (is_value e2) then Mlink (e1, step env e2)
    else begin match e2 with
      | Mclos (cenv, TRcd (l, _), body) ->
        let vl = sel e1 l in
        Mrg (e1, Box (Mrg (cenv, Lrec (l, vl)), body))
      | _ -> failwith "Error: Link must have a module closure with a record import."
    end
  | Mlinkn (e1, e2) ->
    if not (is_value e1) then Mlinkn (step env e1, e2)
    else if not (is_value e2) then Mlinkn (e1, step env e2)
    else begin match e2 with
      | Mclos (cenv, d, body) ->
        let pkg = selpkg e1 d in
        Mrg (e1, Box (Mrg (cenv, pkg), body))
      | _ -> failwith "Error: N-ary link must have a module closure."
    end
  | Inl (ty, e1) -> Inl (ty, step env e1)
  | Inr (ty, e1) -> Inr (ty, step env e1)
  | Case (e1, el, er) ->
    if not (is_value e1) then Case (step env e1, el, er)
    else begin match e1 with
      | Inl (_, v) -> Box (Mrg (env, v), el)
      | Inr (_, v) -> Box (Mrg (env, v), er)
      | _ -> failwith "Error: Case analysis must evaluate to an injection."
    end
  | Fold (ty, e1) -> Fold (ty, step env e1)
  | Unfold e1 ->
    if not (is_value e1) then Unfold (step env e1)
    else begin match e1 with
      | Fold (_, v) -> v
      | _ -> failwith "Error: Unfold applied to a non-fold value."
    end
  | Lit _ | Unit | Clos _ | Mclos _ | Fclos _ -> e

(* Driver for small-step based interpreter. *)
let rec eval' (env : exp) (e : exp) : exp =
  if is_value e then e else eval' env (step env e)