(* A plugin that decorates whatever its peer produces. It cannot name the
   other plugin, load anything, or reach Sys — `peer` is the one route it has,
   and the manager decides where that route leads. *)

import Cap : { log : String -> Top; peer : String -> String }

let run (s : String) : String =
  let noted : Top = Cap.log ("chaining " ^ s) in
  "<" ^ Cap.peer s ^ ">"
