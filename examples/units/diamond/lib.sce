(* The shared provider at the top of the diamond: linked once, its exports
   satisfy every downstream import of `Lib`. *)

module Lib = struct
  let base : Int = 10
  let scale (n : Int) : Int = n * 2
end
