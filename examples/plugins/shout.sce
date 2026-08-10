(* A plugin: a sandboxed functor from the capabilities it is handed to its
   exports. It can log — because the manager passes a log capability — and
   nothing else. *)

import Cap : { log : String -> Top }

let run (msg : String) : String =
  let noted : Top = Cap.log "making some noise" in
  msg ^ "!"
