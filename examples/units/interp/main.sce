(* The driver links the passes. It has its own structurally identical ADT, so
   locally built constructors and Ast's builders are interchangeable. *)

import Ast
import Eval
import Show

type expr = | Lit of Int | Add of expr * expr

let e = Add (Add (Ast.lit 1, Lit 2), Lit 39)

let main : String = Show.expr e ^ " = " ^ Show.int (Eval.run e)
