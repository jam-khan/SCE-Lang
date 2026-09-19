(* Section 2.3: one shop, told in five beats. *)

(* a provider exports more than any one client needs *)
module EU = struct
  let rate : Int = 20
  let ship : Int = 5
end

let secret : Int = 42

(* beat 1 -- a sandboxed client: `rate` is its only dependency. Mentioning
   `secret` or `EU` in the body is a scope error, so the functor is closed and
   can be compiled on its own. *)
module Checkout = sandbox functor (I : { rate : Int }) -> struct
  let total (p : Int) : Int = p + p * I.rate / 100
end

(* beat 2 -- application needs exactly the import; linking finds it.
   `Checkout(EU)` is ill typed: there is no subtyping. *)
module Applied = Checkout({ rate = EU.rate })
module Linked  = link EU with Checkout

(* beat 3 -- the link keeps the provider, so links chain like `ld a.o b.o c.o`:
   Invoice needs `ship` from EU *and* `total` from Checkout. *)
module Invoice = sandbox functor (I : { total : Int -> Int, ship : Int }) -> struct
  let bill (p : Int) : Int = I.total p + I.ship
end
module Shop = linkall Linked with Invoice

(* beat 4 -- linking is an expression: the provider is a run-time argument,
   the import check happened when `open_shop` was compiled. *)
let open_shop (w : sig { rate : Int, ship : Int } end) (p : Int) : Int =
  (linkall (link w with Checkout) with Invoice).bill p

module UK = struct
  let rate : Int = 10
  let ship : Int = 7
end

let main = { applied = Applied.total 100
           , linked  = Linked.total 100
           , kept    = Linked.ship
           , shop    = Shop.bill 100
           , eu      = open_shop EU 100
           , uk      = open_shop UK 100 }
