(* Two versions of Lib in one program: v1 arrives statically through the link
   line, v2 is loaded at a use site. The choice of version is per use site,
   not per program. *)

import Lib
import Loader : { load : String ->
  (({Lib : {version : String; greet : String -> String}}) | {err : String}) }

let main : String =
  let old : String = Lib.greet "world" in
  case Loader.load "libv2.sceo" of
  | inl m -> old ^ " | " ^ m.Lib.greet "world"
  | inr e -> old ^ " | no v2: " ^ e.err
  end
