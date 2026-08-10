(* The shared AST: an iso-recursive union. The .scei spells the type out
   structurally, so passes need no shared nominal declaration. *)

type E = mu a. Int | { l : a; r : a }

module Ast = struct
  let lit (n : Int) : E = (fold (inl n : Int | { l : E; r : E }) : E)
  let add (x : E) (y : E) : E =
    (fold (inr { l = x; r = y } : Int | { l : E; r : E }) : E)
end
