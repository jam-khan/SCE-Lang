(* Peano numerals as an ADT — sugar over the iso-recursive union
   mu a. Top | a. The
   .scei this generates spells the type out structurally, so consumers need
   no shared nominal declaration. *)

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
