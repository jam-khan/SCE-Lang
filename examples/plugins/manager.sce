(* A plugin manager: loads plugin artifacts at run time, interface-checks
   them, and links each against an *attenuated* capability record. The loader
   is itself a capability whose type declares the interface every plugin must
   satisfy — the same structural check the static linker makes, made later. *)

import Sys
import Loader : { load : String ->
  (({Cap : {log : String -> Top}} => {run : String -> String}) | {err : String}) }

module Caps = struct
  (* each plugin logs through its own prefix and can do nothing else *)
  let for_plugin (name : String) : { log : String -> Top } =
    { log = fun (s : String) -> Sys.print ("[" ^ name ^ "] " ^ s) }
end

let plug (name : String) (path : String) : String =
  case Loader.load path of
  | inl p -> open p({ Cap = Caps.for_plugin name }) in run name
  | inr e -> "<" ^ e.err ^ ">"
  end

let main : String =
  plug "shout" "shout.sceo" ^ " " ^
  plug "quiet" "quiet.sceo" ^ " " ^
  plug "ghost" "ghost.sceo"
