(* Recursive linking: `linkrec F` closes a functor whose import is satisfied by
   its own export. It is the mechanization's derived form (`mrec_elab`,
   RecLinking.lean), expanded by the desugarer into

     let F' = F in
     F' { even = fix w (n : Int) : Bool. ((F' { even = w }).even) n }

   so it adds no primitive. The reading is generative: each call through w
   re-applies the functor, so construction work repeats per call. *)

module Parity = functor (X : { even : Int -> Bool }) -> struct
  let odd (n : Int) : Bool = if n = 0 then false else X.even (n - 1)
  let even (n : Int) : Bool = if n = 0 then true else odd (n - 1)
end

module P = linkrec Parity

let main = { even10 = P.even 10, odd10 = P.odd 10, even7 = P.even 7 }
