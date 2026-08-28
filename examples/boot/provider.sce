(* A provider with a construction-time effect: the print fires while the
   unit's exports are being built, not inside any exported function. The
   linker binds each unit exactly once, so linking this into a consumer with
   two imports still prints one line — a composition term that spliced the
   provider into the wire would print once per wired import, plus once. *)

import Sys

module A1 = struct let v : Int = 1 end
module A2 = struct let w : Int = 2 end

let boot : Top = Sys.print "loading provider"
