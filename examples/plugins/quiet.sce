(* A second plugin with the same interface and different behavior. *)

import Cap : { log : String -> Top }

let run (msg : String) : String =
  let noted : Top = Cap.log "staying quiet" in
  "(" ^ msg ^ ")"
