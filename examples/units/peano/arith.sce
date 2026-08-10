(* This unit declares its own N; it matches Nat's because types are compared
   structurally — no nominal identity has to survive separate compilation. *)

import Nat

type N = mu a. Top | a

module Arith = struct
  let two : N = Nat.succ (Nat.succ Nat.zero)
  let three : N = Nat.succ two
  let six : N = Nat.mul two three
end
