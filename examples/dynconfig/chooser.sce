(* Configuration-driven runtime linking: a config file names the artifact to
   load, so swapping the implementation means editing one line of text — no
   recompilation of anything. *)

import Sys
import Loader : { load : String ->
  (({Skin : {render : String -> String}}) | {err : String}) }

(* Local views on the host unions: readfile and load return plain binary
   unions, and an ADT with the same payloads names their branches. *)
type file = | Contents of String | NoFile of {err : String}
type skin = | Loaded of {Skin : {render : String -> String}}
            | Missing of {err : String}

let main : String =
  let path : String =
    match Sys.readfile "skin.txt" with
    | Contents p -> p
    | NoFile e -> "plain.sceo"
    end
  in
  match Loader.load path with
  | Loaded s -> s.Skin.render "hello"
  | Missing e -> "no skin: " ^ e.err
  end
