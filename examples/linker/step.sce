(* A functor unit: the import interface is the record a linker must supply. *)

import Seed : sig { start : Int } end

let bump : Int = Seed.start + 1
