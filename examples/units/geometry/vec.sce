(* A leaf unit of plain arithmetic. *)

module Vec = struct
  let dot (x1 : Int) (y1 : Int) (x2 : Int) (y2 : Int) : Int = x1 * x2 + y1 * y2
  let norm2 (x : Int) (y : Int) : Int = dot x y x y
end
