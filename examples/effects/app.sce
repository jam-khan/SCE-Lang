(* Effects enter through linking: `sys` is a host-built provider unit, and
   this unit gets IO only because the link line grants it. *)

import Sys

module Log = struct
  let info (s : String) : Top = Sys.print ("[app] " ^ s)
end

module Greeter = struct
  let hello (name : String) : String =
    let noted : Top = Log.info ("greeting " ^ name) in
    "hello, " ^ name
end

(* A sandboxed struct cannot reach Sys — or Log — at all: mentioning either
   in here is a *scope error*, not a runtime denial. *)
module Pure = sandbox struct
  let double (n : Int) : Int = n * 2
end

let main : String =
  let a : String = Greeter.hello "world" in
  let b : String = Greeter.hello "again" in
  a ^ " / " ^ b
