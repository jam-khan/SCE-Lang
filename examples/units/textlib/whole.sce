(* The three units of this directory as one program. *)

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
end

module Csv = struct
  let cell (n : Int) : String = Show.int n
  let row (a : Int) (b : Int) (c : Int) : String =
    cell a ^ "," ^ cell b ^ "," ^ cell c
end

module Stats = struct
  let lo : Int = 7
  let hi : Int = 42
end

module Spread = linkall Stats with functor (X : { lo : Int } & { hi : Int }) ->
  struct let range : Int = X.hi - X.lo end

;; Csv.row Spread.range (Spread.range * 2) (0 - Spread.range)
