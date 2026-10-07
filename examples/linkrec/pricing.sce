(* The recursive-linking example of the paper (Section 5.1): Items prices packs
   through its import, Packs prices their contents through its import, and
   `linkrec` closes the cycle through Pricing's `price`. *)

type item = | One of Int | Pack of item * item

module Items = sandbox functor (X : { pack : item -> item -> Int }) -> struct
  let price (i : item) : Int =
    match i with | One p -> p | Pack (a, b) -> X.pack a b end
end

module Packs = sandbox functor (X : { price : item -> Int }) -> struct
  let pack (a : item) (b : item) : Int = (X.price a + X.price b) * 9 / 10
end

module Pricing = functor (X : { price : item -> Int }) ->
  link Packs(X) with Items

module Shop = linkrec Pricing

let main : Int = Shop.price (Pack (One 100, Pack (One 50, One 50)))   (* 171 *)
