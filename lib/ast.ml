type binop =
  | Add
  | Sub
  | Mul
  | Div

type expr =
  | Int of int
  | Binop of binop * expr * expr

let string_of_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"

let rec string_of_expr = function
  | Int n -> string_of_int n
  | Binop (op, lhs, rhs) ->
      Printf.sprintf "(%s %s %s)" (string_of_expr lhs) (string_of_binop op)
        (string_of_expr rhs)
