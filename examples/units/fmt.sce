(* A second leaf unit, so linking exercises more than one provider. *)

module Fmt = struct
  let bracket (s : String) : String = "[" ^ s ^ "]"
  let yes (b : Bool) : String = if b then "yes" else "no"
end
