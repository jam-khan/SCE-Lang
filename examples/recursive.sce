(* Iso-recursive types. `mu a. A` binds `a` in `A`; `fold` needs an ascription
   naming the recursive type, and `unfold` peels one layer off. *)

type Nat = mu a. Top | a

let zero : Nat = (fold (inl () : Top | Nat) : mu a. Top | a)

let succ (n : Nat) : Nat = (fold (inr n : Top | Nat) : mu a. Top | a)

let is_zero (n : Nat) : Bool =
  case unfold n of
    | inl u -> true
    | inr m -> false
  end

;; { z = is_zero zero; one = is_zero (succ zero) }
