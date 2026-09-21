(* Section 5.1: what each extension unlocks, on the shop of Section 2.3. *)

module Checkout = sandbox functor (I : { rate : Int }) -> struct
  let total (p : Int) : Int = p + p * I.rate / 100
end

(* A second client with two imports, wired by label. The provider's order and
   its extra fields are irrelevant; the package follows the client. *)
module Invoice = sandbox functor (I : { total : Int -> Int, ship : Int }) -> struct
  let bill (p : Int) : Int = I.total p + I.ship
end

(* -- unions x n-ary linking: one client, providers with *different*
   interfaces. There is no common supertype to abstract over; each branch
   re-checks the same link against its own provider. The Full branch links a
   second client against the first result: `total` comes from Checkout and
   `ship` from the provider the inner link kept. *)
type region =
  | Flat of sig { rate : Int } end
  | Full of sig { ship : Int, rate : Int } end

let quote (r : region) (p : Int) : Int =
  match r with
  | Flat w -> (link w with Checkout).total p
  | Full w -> (linkall (link w with Checkout) with Invoice).bill p
  end

(* -- recursive types x recursive functions: modules inside data. A route is
   a list of providers, and `cost` links the one compiled client against each
   of them as it recurses. *)
type route = | Stop | Leg of region * route

let rec cost (rs : route) (p : Int) : Int =
  match rs with
  | Stop -> 0
  | Leg (r, rest) -> quote r p + cost rest p
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

(* -- n-ary linking x first-class environments: `?` is a provider like any
   other, so a module can link a client against everything it has declared so
   far. The result
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

(* -- recursive linking x sandboxing: a cycle between two closed clients.
   Items imports what Packs exports and the reverse; neither names the other,
   so each can be compiled alone. A third party closes the cycle: given
   `price`, Packs provides the `pack` that Items is linked against, and the
   knot over `price` is an ordinary let rec. *)
type item = | One of Int | Pack of item * item

module Items = sandbox functor (X : { pack : item -> item -> Int }) -> struct
  let price (i : item) : Int =
    match i with | One p -> p | Pack (a, b) -> X.pack a b end
end

module Packs = sandbox functor (X : { price : item -> Int }) -> struct
  let pack (a : item) (b : item) : Int = (X.price a + X.price b) * 9 / 10
end

module Pricing = functor (X : { price : item -> Int }) -> link Packs(X) with Items

let rec price (i : item) : Int = (Pricing({ price = price })).price i

let flat = Flat (struct let rate : Int = 8 end)
let full = Full (struct let ship : Int = 5 let rate : Int = 20 end)

let main = { flat    = quote flat 100
           , full    = quote full 100
           , trip    = cost (Leg (flat, Leg (full, Stop))) 100
           , redeem  = redeem (Then (TenOff, Then (HalfOff, Done))) 100
           , audit   = audit (evolve 10) 3
           , bill    = (linkall World with Invoice).bill 100
           , desk    = Shop.Desk.bill 100
           , nested  = price (Pack (One 100, Pack (One 50, One 50))) }
