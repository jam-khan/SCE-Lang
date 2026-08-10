(* Applies the imported functor: under wasm-level linking, the closure was
   built by shapes.wasm's instance and is called from this unit's code. *)

import Shapes
import Scale

module Doubler = Scale({ k = 2 })

let main : Int = Doubler.by (Shapes.area 3 4) + Shapes.diag2 3 4
