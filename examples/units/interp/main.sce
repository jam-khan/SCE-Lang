(* The driver links the constructors to the passes. Each pass is a separately
   compiled unit against the same structural AST type. *)

import Ast
import Eval
import Show

let e = Ast.add (Ast.add (Ast.lit 1) (Ast.lit 2)) (Ast.lit 39)

let main : String = Show.expr e ^ " = " ^ Show.int (Eval.run e)
