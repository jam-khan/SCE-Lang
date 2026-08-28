(* A functor unit: the import interface is the record a linker must supply. *)

import Seed : { start : Int }

let bump : Int = Seed.start + 1
