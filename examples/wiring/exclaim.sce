(* A plugin that only shouts. Its peer capability goes unused — what the
   manager wires in is invisible from here. *)

import Cap : { log : String -> Top; peer : String -> String }

let run (s : String) : String =
  let noted : Top = Cap.log ("exclaiming " ^ s) in
  s ^ "!"
