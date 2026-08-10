(* The three units of this directory as one program. *)

module Vec = struct
  let dot (x1 : Int) (y1 : Int) (x2 : Int) (y2 : Int) : Int = x1 * x2 + y1 * y2
  let norm2 (x : Int) (y : Int) : Int = dot x y x y
end

module Shapes = struct
  let area (w : Int) (h : Int) : Int = w * h
  let diag2 (w : Int) (h : Int) : Int = Vec.norm2 w h
end

module Scale (K : { k : Int }) = struct
  let by (n : Int) : Int = n * K.k
end

module Doubler = Scale({ k = 2 })

;; Doubler.by (Shapes.area 3 4) + Shapes.diag2 3 4
