(* Version 2: the same module name, the same interface, new behavior.
   Linking both versions statically is rejected — the label would be
   ambiguous — but nothing stops v2 from being *loaded* at a use site. *)

module Lib = struct
  let version : String = "v2"
  let greet (s : String) : String = "HELLO, " ^ s ^ " (v2)"
end
