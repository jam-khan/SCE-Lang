(* Delegation is manager-wired: chain's `peer` capability *is* exclaim's run
   function. The plugins never see each other — one plugin's authority over
   another exists only because the host built it into a capability record. *)

import Sys
import Loader : { load : String ->
  (({Cap : {log : String -> Top; peer : String -> String}}
      => {run : String -> String}) | {err : String}) }

module Caps = struct
  let log_for (name : String) : String -> Top =
    fun (s : String) -> Sys.print ("[" ^ name ^ "] " ^ s)
end

let idpeer (s : String) : String = s

let main : String =
  case Loader.load "exclaim.sceo" of
  | inl p ->
    let ex = p({ Cap = { log = Caps.log_for "exclaim"; peer = idpeer } }) in
    (case Loader.load "chain.sceo" of
     | inl q ->
       let ch = q({ Cap = { log = Caps.log_for "chain"; peer = ex.run } }) in
       ch.run "hi"
     | inr e -> "<" ^ e.err ^ ">"
     end)
  | inr e -> "<" ^ e.err ^ ">"
  end
