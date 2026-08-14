(* Literals, primitives, functions and records. *)

type Point = { x : Int, y : Int }

let origin : Point = { x = 0, y = 0 }

let move (p : Point) (dx : Int) : Point = { x = p.x + dx, y = p.y }

let rec fact (n : Int) : Int = if n <= 1 then 1 else n * fact (n - 1)

let describe (p : Point) : String =
  if p.x = 0 && p.y = 0 then "origin" else "somewhere else"

let main = { shifted = (move origin 7).x
   , five    = fact 5
   , what    = describe origin
   , joined  = "a" ^ "b" ^ "c"
   }
