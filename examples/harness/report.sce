(* A component written against an interface, not a world: everything it can
   reach is in Env. Which world that is — live or canned — is its caller's
   decision, per instantiation. *)

import Env : { fetch : String -> String }

let run (k : String) : String = "data(" ^ k ^ ") = " ^ Env.fetch k
