(* Structures, functors, sandboxing and linking.

   A `struct` is a dependent merge chain, so a declaration can use the ones
   before it; its type is a signature, `sig ... end`. A `sandbox struct` is a
   struct boxed under the empty environment, so nothing from outside is
   reachable inside it. *)

module Counter = struct
  let start : Int = 10
  let bump (n : Int) : Int = n + 1
  let started : Int = bump start
end

module Secret = sandbox struct
  let key : Int = 42
end

(* A functor's parameter is its import interface; `X.start` resolves through
   the signature written right here. *)
module Doubler (X : { start : Int }) = struct
  let doubled : Int = X.start * 2
end

(* There is no subtyping: `Doubler(Counter)` would be rejected, because
   Counter's type is a signature, and wider than `{ start : Int }` besides.
   Direct application needs an argument of exactly the import type. *)
module Applied = Doubler({ start = Counter.start })

(* Linking is the mechanism that does cope with a wider module: it looks the
   imported labels up in it and keeps both halves in the result. *)
module Linked =
  link Counter with functor (X : { start : Int }) -> struct
    let next : Int = X.start + 1
  end

(* `open` brings a module's fields into scope for what follows. *)
open Counter

let main = { started = started
   , doubled = Applied.doubled
   , next    = Linked.next
   , secret  = Secret.key
   }
