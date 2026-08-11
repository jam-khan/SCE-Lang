(* An evaluation pass. It imports nothing: it redeclares the type and matches
   on the structure — compatibility with Ast's values is structural. *)

type expr = | Lit of Int | Add of expr * expr

module Eval = struct
  let rec run (e : expr) : Int =
    match e with
    | Lit n -> n
    | Add (a, b) -> run a + run b
    end
end
