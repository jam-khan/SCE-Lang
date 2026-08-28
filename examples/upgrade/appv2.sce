(* The upgrade: a functor whose import interface *is* the migration contract.
   It cannot run without being handed the old version's state, and the types
   say exactly which pieces it inherits. *)

import Old : { motto : String, owner : String }

let banner : String = "v2 for " ^ Old.owner ^ " (was: " ^ Old.motto ^ ")"
let owner : String = Old.owner
