(* The four units of this directory as one program — the twin the test suite
   diffs every linking path against. *)

type E = mu a. Int | { l : a; r : a }

module Ast = struct
  let lit (n : Int) : E = (fold (inl n : Int | { l : E; r : E }) : E)
  let add (x : E) (y : E) : E =
    (fold (inr { l = x; r = y } : Int | { l : E; r : E }) : E)
end

module Eval = struct
  let rec run (e : E) : Int =
    case unfold e of
    | inl n -> n
    | inr p -> run p.l + run p.r
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
  let rec expr (e : E) : String =
    case unfold e of
    | inl n -> int n
    | inr p -> "(" ^ expr p.l ^ " + " ^ expr p.r ^ ")"
    end
end

let e = Ast.add (Ast.add (Ast.lit 1) (Ast.lit 2)) (Ast.lit 39)

;; Show.expr e ^ " = " ^ Show.int (Eval.run e)
