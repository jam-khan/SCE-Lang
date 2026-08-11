(* The driver: lex, parse, normalize, print. Parse failure is a value the
   program handles, and the fuel bound makes Omega answer instead of hang. *)

import Lex
import Parse
import Eval
import Pretty

type term   = | Var of String | Lam of String * term | App of term * term
type parsed = | Ok of term | Err of String

let run (src : String) : String =
  match Parse.parse (Lex.lex src) with
  | Ok t -> Pretty.print (Eval.norm 1000 t)
  | Err m -> "parse error: " ^ m
  end

let main : String =
  run "(\\m.\\n.\\f.\\x. m f (n f x)) (\\f.\\x. f (f x)) (\\f.\\x. f (f x))"
  ^ "  ;  " ^ run "(\\x.\\y. x) a b"
  ^ "  ;  " ^ run "\\x. (x"
