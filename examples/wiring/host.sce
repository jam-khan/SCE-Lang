(* Delegation is manager-wired: chain's `peer` capability *is* exclaim's run
   function. The plugins never see each other — one plugin's authority over
   another exists only because the host built it into a capability record. *)

import Sys
import Loader : { load : String ->
  (({Cap : {log : String -> Top; peer : String -> String}}
      => {run : String -> String}) | {err : String}) }

type loaded =
  | Plugin of (({Cap : {log : String -> Top; peer : String -> String}})
                 => {run : String -> String})
  | Failed of {err : String}

module Caps = struct
  let log_for (name : String) : String -> Top =
    fun (s : String) -> Sys.print ("[" ^ name ^ "] " ^ s)
end

let idpeer (s : String) : String = s

let main : String =
  match Loader.load "exclaim.sceo" with
  | Plugin p ->
    let ex = p({ Cap = { log = Caps.log_for "exclaim"; peer = idpeer } }) in
    (match Loader.load "chain.sceo" with
     | Plugin q ->
       let ch = q({ Cap = { log = Caps.log_for "chain"; peer = ex.run } }) in
       ch.run "hi"
     | Failed e -> "<" ^ e.err ^ ">"
     end)
  | Failed e -> "<" ^ e.err ^ ">"
  end
