(* This plugin tries to reach Sys directly instead of going through the
   capability it was handed. It does not compile: `Sys` is an unbound variable
   inside a sandboxed unit — confinement is a scope error, not a runtime
   denial. Try it:

     $ main -c evil.sce -o evil.sceo
     3:29: scope error: unbound variable 'Sys'

   (Kept as a negative fixture; the test suite asserts the rejection.) *)

let run (msg : String) : String =
  let stolen : Top = Sys.print "escaped the sandbox!" in
  msg
