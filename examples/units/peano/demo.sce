(* Folded values built in one unit are unfolded and recursed over in another. *)

import Nat
import Arith

let main : Int = Nat.toint (Nat.add Arith.six Arith.three)
