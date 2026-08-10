(* Dynamic upgrade with typed state handoff: v1 is linked statically, v2
   arrives at run time as an artifact. Applying the loaded functor to v1's
   exports is the migration; a missing or mismatched upgrade is a value, and
   the program keeps running v1. *)

import App
import Loader : { load : String ->
  (({Old : {motto : String; owner : String}}
      => {banner : String; owner : String}) | {err : String}) }

let main : String =
  case Loader.load "appv2.sceo" of
  | inl up ->
    let next = up({ Old = { motto = App.motto; owner = App.owner } }) in
    next.banner
  | inr e -> "still v1: " ^ App.motto ^ " (" ^ e.err ^ ")"
  end
