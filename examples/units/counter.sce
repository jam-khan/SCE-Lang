(* A leaf unit: no imports. Compiling it writes Counter.scei next to the
   artifact, so downstream units can say just `import Counter`. *)

module Counter = struct
  let start : Int = 10
  let bump (n : Int) : Int = n + 1
end
