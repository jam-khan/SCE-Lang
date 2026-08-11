(* The shared AST as an algebraic data type. The .scei spells the type out
   structurally, so passes need no shared nominal declaration. *)

type expr = | Lit of Int | Add of expr * expr

module Ast = struct
  let lit (n : Int) : expr = Lit n
  let add (x : expr) (y : expr) : expr = Add (x, y)
end
