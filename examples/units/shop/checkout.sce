(* A client compiled against Region.scei alone. *)

import Region

module Checkout = struct
  let total (p : Int) : Int = p + p * Region.rate / 100
end
