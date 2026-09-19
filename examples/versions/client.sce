(* Two versions of Lib in one program: v1 arrives statically through the link
   line, v2 is loaded at a use site. The choice of version is per use site,
   not per program. *)

import Lib
import Loader : { load : String ->
  ((sig {Lib : sig {version : String, greet : String -> String} end} end) | {err : String}) }

type fetched =
  | V2 of sig {Lib : sig {version : String, greet : String -> String} end} end
  | NoV2 of {err : String}

let main : String =
  let old : String = Lib.greet "world" in
  match Loader.load "libv2.sceo" with
  | V2 m -> old ^ " | " ^ m.Lib.greet "world"
  | NoV2 e -> old ^ " | no v2: " ^ e.err
  end
