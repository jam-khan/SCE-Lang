(* Configuration-driven runtime linking: a config file names the artifact to
   load, so swapping the implementation means editing one line of text — no
   recompilation of anything. *)

import Sys
import Loader : { load : String ->
  (({Skin : {render : String -> String}}) | {err : String}) }

let main : String =
  let path : String =
    case Sys.readfile "skin.txt" of
    | inl p -> p
    | inr e -> "plain.sceo"
    end
  in
  case Loader.load path of
  | inl s -> s.Skin.render "hello"
  | inr e -> "no skin: " ^ e.err
  end
