(* This unit declares its own ADT with its own constructor names; it matches
   Nat's because types are compared structurally — neither the type nor the
   constructors have to survive separate compilation. *)

import Nat

type nat = 
  | Zero 
  | Next of nat

module Arith = struct
  let two : nat = Next (Next Zero)
  let three : nat = Nat.succ two
  let six : nat = Nat.mul two three
end
