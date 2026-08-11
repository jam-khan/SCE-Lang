(* Normal-order reduction with capture-avoiding substitution and a fuel
   bound, so a diverging term answers instead of hanging. Imports nothing. *)

type term = | Var of String | Lam of String * term | App of term * term
type opt  = | ONone | OSome of term

module Eval = struct
  let rec free (x : String) (t : term) : Bool =
    match t with
    | Var y -> x = y
    | Lam (y, b) -> if x = y then false else free x b
    | App (f, a) -> free x f || free x a
    end
  let rec fresh (x : String) (v : term) (b : term) : String =
    if free x v || free x b then fresh (x ^ "'") v b else x
  let rec subst (x : String) (v : term) (t : term) : term =
    match t with
    | Var y -> if x = y then v else Var y
    | Lam (y, b) ->
      if x = y then Lam (y, b)
      else if free y v then
        let z = fresh (y ^ "'") v b in
        Lam (z, subst x v (subst y (Var z) b))
      else Lam (y, subst x v b)
    | App (f, a) -> App (subst x v f, subst x v a)
    end
  let rec step (t : term) : opt =
    match t with
    | Var x -> ONone
    | Lam (x, b) ->
      (match step b with
       | OSome b2 -> OSome (Lam (x, b2))
       | ONone -> ONone
       end)
    | App (f, a) ->
      (match f with
       | Lam (x, b) -> OSome (subst x a b)
       | _ ->
         (match step f with
          | OSome f2 -> OSome (App (f2, a))
          | ONone ->
            (match step a with
             | OSome a2 -> OSome (App (f, a2))
             | ONone -> ONone
             end)
          end)
       end)
    end
  let rec norm (fuel : Int) (t : term) : term =
    if fuel = 0 then t
    else
      match step t with
      | OSome t2 -> norm (fuel - 1) t2
      | ONone -> t
      end
end
