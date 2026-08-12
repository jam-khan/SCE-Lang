(* Two imports from the same provider: the wire projects two labels, and the
   provider's boot line must still appear exactly once. *)

import A1
import A2

let main : Int = A1.v + A2.w
