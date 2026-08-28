(* The running version: a leaf unit, linked statically. Its exports are the
   state a future version will inherit. *)

module App = struct
  let motto : String = "keep going"
  let owner : String = "jam"
end
