(* Section 5.1: what each extension unlocks, on the shop of Section 2.3. *)

module Checkout = sandbox functor (I : { rate : Int }) -> struct
  let total (p : Int) : Int = p + p * I.rate / 100
end

(* -- unions: one client, providers with *different* interfaces. There is no
   common supertype to abstract over; each branch re-checks the same link
   against its own provider. *)
type region =
  | Flat of sig { rate : Int } end
  | Full of sig { ship : Int, rate : Int, vat : Int } end

let quote (r : region) (p : Int) : Int =
  match r with
  | Flat w -> (link w with Checkout).total p
  | Full w -> (link w with Checkout).total p + w.ship
  end

(* -- recursive types x linking: a live provider. Each generation is a module
   that carries the next one; the client is compiled once and re-linked
   against every generation as the program runs. *)
type gen = mu a. sig { rate : Int, next : Top -> a } end

let rec evolve (r : Int) : gen =
  (fold (struct
     let rate : Int = r
     let next (u : Top) : gen = evolve (r + 5)
   end) : gen)

let rec audit (g : gen) (k : Int) : Int =
  if k = 0 then 0
  else (link (unfold g) with Checkout).total 100 + audit ((unfold g).next ()) (k - 1)

(* -- recursive types x sandboxing: modules inside data. A coupon is a
   sandboxed functor; a campaign is a list of them, run by an ordinary fold.
   No coupon can see the shop or the other coupons -- only the price it is
   handed. *)
type campaign =
  | Done
  | Then of ({ price : Int } => sig { price : Int } end) * campaign

let rec redeem (c : campaign) (p : Int) : Int =
  match c with
  | Done -> p
  | Then (coupon, rest) -> redeem rest (coupon({ price = p })).price
  end

module TenOff  = sandbox functor (I : { price : Int }) -> struct let price : Int = I.price - 10 end
module HalfOff = sandbox functor (I : { price : Int }) -> struct let price : Int = I.price / 2 end

(* -- n-ary linking: several imports, wired by label. The provider's order
   and its extra fields are irrelevant; the package follows the client. *)
module Invoice = sandbox functor (I : { total : Int -> Int, ship : Int }) -> struct
  let bill (p : Int) : Int = I.total p + I.ship
end
(* x first-class environments: `?` is a provider like any other, so a module
   can link a client against everything it has declared so far. The result
   keeps that environment, so the next client links against the first. *)
module Shop = struct
  let rate : Int = 20
  let ship : Int = 5
  module Till = link ? with Checkout
  module Desk = linkall Till with Invoice
end

module World = struct
  let vat  : Int = 0
  let ship : Int = 5
  let total (p : Int) : Int = p + 1
end

(* -- recursive linking: a module whose import is its own export. Before the
   knot is tied the import is just a parameter, so one step of the recursion
   can be tested against a stub; tying it is an ordinary let rec. *)
module Parity = functor (X : { even : Int -> Bool }) -> struct
  let odd  (n : Int) : Bool = if n = 0 then false else X.even (n - 1)
  let even (n : Int) : Bool = if n = 0 then true  else odd (n - 1)
end
let stubbed : Bool = (Parity({ even = fun (n : Int) -> true })).odd 7
let rec even (n : Int) : Bool = (Parity({ even = even })).even n

let main = { flat    = quote (Flat (struct let rate : Int = 8 end)) 100
           , full    = quote (Full (struct let ship : Int = 5 let rate : Int = 20 let vat : Int = 0 end)) 100
           , redeem  = redeem (Then (TenOff, Then (HalfOff, Done))) 100
           , audit   = audit (evolve 10) 3
           , bill    = (linkall World with Invoice).bill 100
           , desk    = Shop.Desk.bill 100
           , stubbed = stubbed
           , even10  = even 10 }
