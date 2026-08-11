(* The link step, written in the language it links: extend the world with the
   provider, wire its export into the import record, keep both halves. The
   builtin `link` elaborates to exactly this shape, so the two must agree —
   compared here at run time, against a functor that arrived from disk. *)

import Loader : { load : String ->
  (({Seed : {start : Int}} => {bump : Int}) | {err : String}) }

type loaded =
  | Step of (({Seed : {start : Int}}) => {bump : Int})
  | Failed of {err : String}

module Prov = struct let start : Int = 10 end

(* the builtin construct, as the reference *)
module Ref = link Prov with functor (X : { start : Int }) -> struct
  let bump : Int = X.start + 1
end

let main : String =
  match Loader.load "step.sceo" with
  | Step f ->
    let linked = Prov ,,, f({ Seed = { start = Prov.start } }) in
    if (linked.bump = Ref.bump) && (linked.start = Prov.start)
    then "hand-written link = builtin link, both halves kept"
    else "disagreement"
  | Failed e -> "<" ^ e.err ^ ">"
  end
