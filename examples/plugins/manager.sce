(* A plugin manager: loads plugin artifacts at run time, interface-checks
   them, and links each against an *attenuated* capability record. The loader
   is itself a capability whose type declares the interface every plugin must
   satisfy — the same structural check the static linker makes, made later. *)

import Sys
import Loader : { load : String ->
  (({Cap : {log : String -> Top}} => {run : String -> String}) | {err : String}) }

(* A local view on the loader's union: constructor names are surface-only, so
   an ADT with the same payloads matches the host's result type exactly. *)
type loaded =
  | Plugin of (({Cap : {log : String -> Top}}) => {run : String -> String})
  | Failed of {err : String}

module Caps = struct
  (* each plugin logs through its own prefix and can do nothing else *)
  let for_plugin (name : String) : { log : String -> Top } =
    { log = fun (s : String) -> Sys.print ("[" ^ name ^ "] " ^ s) }
end

(* Linking at the use site: the capability record is built under the label
   the plugin imports, `link` wires it in and keeps both halves, and `run` is
   projected out of the result — dynamic linking as an ordinary expression. *)
let plug (name : String) (path : String) : String =
  match Loader.load path with
  | Plugin p -> (link { Cap = Caps.for_plugin name } with p).run name
  | Failed e -> "<" ^ e.err ^ ">"
  end

let main : String =
  plug "shout" "shout.sceo" ^ " " ^
  plug "quiet" "quiet.sceo" ^ " " ^
  plug "ghost" "ghost.sceo"
