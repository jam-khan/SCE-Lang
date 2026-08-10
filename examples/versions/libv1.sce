(* Version 1 of a library. *)

module Lib = struct
  let version : String = "v1"
  let greet (s : String) : String = "hello, " ^ s ^ " (v1)"
end
