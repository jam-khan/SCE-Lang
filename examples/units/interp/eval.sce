(* An evaluation pass. It imports nothing: it redeclares E and works on the
   structure directly — compatibility with Ast's values is structural. *)

type E = mu a. Int | { l : a; r : a }

module Eval = struct
  let rec run (e : E) : Int =
    case unfold e of
    | inl n -> n
    | inr p -> run p.l + run p.r
    end
end
