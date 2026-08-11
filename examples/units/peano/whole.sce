(* The three units of this directory as one program. *)

type nat = | Z | S of nat

module Nat = struct
  let zero : nat = Z
  let succ (n : nat) : nat = S n
  let rec add (m : nat) (n : nat) : nat =
    match m with
    | Z -> n
    | S p -> S (add p n)
    end
  let rec mul (m : nat) (n : nat) : nat =
    match m with
    | Z -> Z
    | S p -> add n (mul p n)
    end
  let rec toint (n : nat) : Int =
    match n with
    | Z -> 0
    | S p -> 1 + toint p
    end
end

module Arith = struct
  let two : nat = S (S Z)
  let three : nat = Nat.succ two
  let six : nat = Nat.mul two three
end

;; Nat.toint (Nat.add Arith.six Arith.three)
