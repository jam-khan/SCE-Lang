(* Exports a plain module *and* a functor. The functor's .scei is a signature
   ({k : Int} => {by : Int -> Int}), so a consumer unit can import it and apply
   it — a functor value crossing a unit boundary. *)

import Vec

module Shapes = struct
  let area (w : Int) (h : Int) : Int = w * h
  let diag2 (w : Int) (h : Int) : Int = Vec.norm2 w h
end

module Scale (K : { k : Int }) = struct
  let by (n : Int) : Int = n * K.k
end
