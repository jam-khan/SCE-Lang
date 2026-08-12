(* The link step, written in the language it links — and checked against the
   builtin on the *same* loaded functor. `link P with f` means: extend the
   world with the provider, wire its export into the import record, keep both
   halves. The hand-written merge below is that sentence spelled out; the
   builtin elaborates to the same composition shape, so the two must agree —
   compared field by field on both halves, which at these types is the whole
   value (`=` is primitive-only). *)

import Loader : { load : String ->
  (({Seed : {start : Int}} => {bump : Int}) | {err : String}) }

type loaded =
  | Step of (({Seed : {start : Int}}) => {bump : Int})
  | Failed of {err : String}

module P = struct
  module Seed = struct let start : Int = 10 end
end

let main : String =
  match Loader.load "step.sceo" with
  | Step f ->
    let builtin = link P with f in
    let byhand = P ,,, f({ Seed = P.Seed }) in
    if (builtin.bump = byhand.bump)
       && (builtin.Seed.start = byhand.Seed.start)
       && (byhand.bump = P.Seed.start + 1)
    then "hand-written link = builtin link, both halves kept"
    else "disagreement"
  | Failed e -> "<" ^ e.err ^ ">"
  end
