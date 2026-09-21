(* Needs both earlier units: the link keeps the provider next to the client. *)

import Region
import Checkout

let main : Int = Checkout.total 100 + Region.ship
