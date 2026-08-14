(* The three units of this directory as one program — the twin the test suite
   diffs every linking path against. *)

module Counter = struct
  let start : Int = 10
  let bump (n : Int) : Int = n + 1
end

module Fmt = struct
  let bracket (s : String) : String = "[" ^ s ^ "]"
  let yes (b : Bool) : String = if b then "yes" else "no"
end

module App = struct
  let level : Int = Counter.bump (Counter.bump Counter.start)
  let big : Bool = level > 11
end

let main = Fmt.bracket (Fmt.yes App.big)
