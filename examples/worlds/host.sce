(* Environments are values. One arrives from disk and is entered with `box`;
   another is the current world, captured with `?` and re-entered when the
   load fails. Inside a box the body sees only the world it was given — names
   from out here do not resolve. *)

import Loader : { load : String ->
  (({Theme : {decorate : String -> String}}) | {err : String}) }

type loaded =
  | World of {Theme : {decorate : String -> String}}
  | NoWorld of {err : String}

module Base = struct let decorate (s : String) : String = s end

(* the world as of this line, reified — Base is a field of it *)
let snap = ?

let themed (path : String) : String =
  match Loader.load path with
  | World w -> box w in ?.Theme.decorate "hello"
  | NoWorld e -> box snap in ?.Base.decorate "hello"
  end

let main : String = themed "fancy.sceo" ^ " / " ^ themed "ghost.sceo"
