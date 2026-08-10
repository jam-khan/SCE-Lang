(* A middle unit: consumes Show, is consumed by summary. *)

import Show

module Csv = struct
  let cell (n : Int) : String = Show.int n
  let row (a : Int) (b : Int) (c : Int) : String =
    cell a ^ "," ^ cell b ^ "," ^ cell c
end
