(* Both linking levels in one program: this unit is linked by the toolchain,
   while its body links Stats with a functor using the language's own
   first-class `linkall`. *)

import Csv

module Stats = struct
  let lo : Int = 7
  let hi : Int = 42
end

module Spread = linkall Stats with functor (X : { lo : Int } & { hi : Int }) ->
  struct let range : Int = X.hi - X.lo end

let main : String = Csv.row Spread.range (Spread.range * 2) (0 - Spread.range)
