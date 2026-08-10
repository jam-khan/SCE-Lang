(* The consumer: both imports resolve against the generated .scei files.
   This whole file compiles to a sandboxed functor from its imports to its
   exports — linking applies it to projections wired out of the providers. *)

import Counter
import Fmt

module App = struct
  let level : Int = Counter.bump (Counter.bump Counter.start)
  let big : Bool = level > 11
end

let main : String = Fmt.bracket (Fmt.yes App.big)
