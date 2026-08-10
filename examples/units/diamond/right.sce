(* The other side: uses Lib's function. Both sides check against the same
   Lib.scei, and linking installs a single copy of Lib for both. *)

import Lib

module Right = struct
  let value : Int = Lib.scale Lib.base
end
