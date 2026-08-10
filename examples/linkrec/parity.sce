(* Recursive linking as a derived form: a functor whose import is satisfied by
   its own export, tied with an ordinary let rec. This is the mechanization's
   linkrec (Theorem 31) written in surface syntax — no new primitive. *)

module Parity = functor (X : { even : Int -> Bool }) -> struct
  let odd (n : Int) : Bool = if n = 0 then false else X.even (n - 1)
  let even (n : Int) : Bool = if n = 0 then true else odd (n - 1)
end

(* The knot: the import each application receives is the function being
   defined, so the module's own export flows back in as its import. *)

let rec even (n : Int) : Bool = 
   let m = Parity({ even = even }) in 
   m.even n

let odd (n : Int) : Bool = 
   let m = Parity({ even = even }) in 
   m.odd n

;; { even10 = even 10; odd10 = odd 10; even7 = even 7 }
