(* One loaded artifact, two worlds: the same functor is instantiated against
   a live environment backed by Sys and a canned in-memory one. Environments
   are records, instantiation is application — mocking without a framework. *)

import Sys
import Loader : { load : String ->
  (({Env : {fetch : String -> String}} => {run : String -> String})
    | {err : String}) }

let live (k : String) : String =
  case Sys.readfile k of
  | inl s -> s
  | inr e -> "<missing>"
  end

let canned (k : String) : String = "42"

let main : String =
  case Loader.load "report.sceo" of
  | inl f ->
    let mock = f({ Env = { fetch = canned } }) in
    let prod = f({ Env = { fetch = live } }) in
    mock.run "answer" ^ " / " ^ prod.run "data.txt"
  | inr e -> "<" ^ e.err ^ ">"
  end
