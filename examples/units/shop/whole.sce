(* The same program as one file: linking written as an expression. *)

module World = struct
  module Region = struct
    let rate : Int = 20
    let ship : Int = 5
  end
end

module Checkout = sandbox functor (I : { Region : sig { rate : Int, ship : Int } end }) -> struct
  module Checkout = struct
    let total (p : Int) : Int = p + p * I.Region.rate / 100
  end
end

module Invoice = sandbox functor
    (I : { Region : sig { rate : Int, ship : Int } end
         , Checkout : sig { total : Int -> Int } end }) -> struct
  let main : Int = I.Checkout.total 100 + I.Region.ship
end

let main : Int =
  (linkall (link World with Checkout) with Invoice).main
