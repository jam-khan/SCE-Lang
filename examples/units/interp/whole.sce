(* The four units of this directory as one program — the twin the test suite
   diffs every linking path against. *)

type expr = | Lit of Int | Add of expr * expr

module Ast = struct
  let lit (n : Int) : expr = Lit n
  let add (x : expr) (y : expr) : expr = Add (x, y)
end

module Eval = struct
  let rec run (e : expr) : Int =
    match e with
    | Lit n -> n
    | Add (a, b) -> run a + run b
    end
end

module Show = struct
  let digit (d : Int) : String =
    if d = 0 then "0" else if d = 1 then "1" else if d = 2 then "2"
    else if d = 3 then "3" else if d = 4 then "4" else if d = 5 then "5"
    else if d = 6 then "6" else if d = 7 then "7" else if d = 8 then "8"
    else "9"
  let rec go (n : Int) : String =
    if n < 10 then digit n else go (n / 10) ^ digit (n mod 10)
  let int (n : Int) : String =
    if n < 0 then "-" ^ go (0 - n) else go n
  let rec expr (e : expr) : String =
    match e with
    | Lit n -> int n
    | Add (a, b) -> "(" ^ expr a ^ " + " ^ expr b ^ ")"
    end
end

let e = Add (Add (Ast.lit 1, Lit 2), Lit 39)

let main = Show.expr e ^ " = " ^ Show.int (Eval.run e)
