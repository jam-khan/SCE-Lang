open Ast

let rec eval = function
  | Int n -> n
  | Binop (op, lhs, rhs) -> (
      let l = eval lhs and r = eval rhs in
      match op with
      | Add -> l + r
      | Sub -> l - r
      | Mul -> l * r
      | Div -> l / r)
