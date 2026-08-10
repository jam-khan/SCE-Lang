(* Peano numerals over an iso-recursive type. The .scei this generates spells
   the mu-type out structurally, so consumers need no shared nominal type. *)

type N = mu a. Top | a

module Nat = struct
  let zero : N = (fold (inl () : Top | N) : N)
  let succ (n : N) : N = (fold (inr n : Top | N) : N)
  let rec add (m : N) (n : N) : N =
    case unfold m of
    | inl u -> n
    | inr p -> (fold (inr (add p n) : Top | N) : N)
    end
  let rec mul (m : N) (n : N) : N =
    case unfold m of
    | inl u -> zero
    | inr p -> add n (mul p n)
    end
  let rec toint (n : N) : Int =
    case unfold n of
    | inl u -> 0
    | inr p -> 1 + toint p
    end
end
