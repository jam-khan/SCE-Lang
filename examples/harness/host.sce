(* One loaded artifact, two worlds: the same functor is instantiated against
   a live environment backed by Sys and a canned in-memory one. Environments
   are records, instantiation is application — mocking without a framework. *)

import Sys
import Loader : { load : String ->
  (({Env : {fetch : String -> String}} => {run : String -> String})
    | {err : String}) }

type loaded =
  | Report of (({Env : {fetch : String -> String}}) => {run : String -> String})
  | Failed of {err : String}
type file = | Contents of String | NoFile of {err : String}

let live (k : String) : String =
  match Sys.readfile k with
  | Contents s -> s
  | NoFile e -> "<missing>"
  end

let canned (k : String) : String = "42"

let main : String =
  match Loader.load "report.sceo" with
  | Report f ->
    let mock = f({ Env = { fetch = canned } }) in
    let prod = f({ Env = { fetch = live } }) in
    mock.run "answer" ^ " / " ^ prod.run "data.txt"
  | Failed e -> "<" ^ e.err ^ ">"
  end
