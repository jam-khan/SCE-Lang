(* The four units of this directory as one program — the twin the test suite
   diffs every linking path against. *)

module Lib = struct
  let base : Int = 10
  let scale (n : Int) : Int = n * 2
end

module Left = struct
  let value : Int = Lib.base + 1
end

module Right = struct
  let value : Int = Lib.scale Lib.base
end

let main = Left.value + Right.value
