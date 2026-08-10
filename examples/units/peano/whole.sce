(* The three units of this directory as one program. *)

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

module Arith = struct
  let two : N = Nat.succ (Nat.succ Nat.zero)
  let three : N = Nat.succ two
  let six : N = Nat.mul two three
end

;; Nat.toint (Nat.add Arith.six Arith.three)
