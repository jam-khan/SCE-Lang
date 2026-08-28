(* A world on disk: a leaf artifact whose value will be entered with box. *)

module Theme = struct
  let decorate (s : String) : String = "** " ^ s ^ " **"
end
