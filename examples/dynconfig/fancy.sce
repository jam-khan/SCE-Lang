(* Same interface, different implementation. *)

module Skin = struct
  let render (s : String) : String = "** " ^ s ^ " **"
end
