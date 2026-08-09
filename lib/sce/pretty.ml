(* Printers for λSCE types. *)
open Ast

(* Precedence levels, loosest first: 0 signature/arrow, 1 union,
   2 intersection, 3 atom. *)
let rec typ_prec p t =
  let paren need s = if need then "(" ^ s ^ ")" else s in
  match t with
  | TInt -> "Int"
  | TBool -> "Bool"
  | TString -> "String"
  | TTop -> "Top"
  | TVar n -> Printf.sprintf "a%d" n
  | TRcd (l, a) -> Printf.sprintf "{%s : %s}" l (typ_prec 0 a)
  | TArr (a, b) ->
    paren (p > 0) (Printf.sprintf "%s -> %s" (typ_prec 1 a) (typ_prec 0 b))
  | TOr (a, b) ->
    paren (p > 1) (Printf.sprintf "%s | %s" (typ_prec 1 a) (typ_prec 2 b))
  | TAnd (a, b) ->
    paren (p > 2) (Printf.sprintf "%s & %s" (typ_prec 2 a) (typ_prec 3 b))
  | TMu a -> paren (p > 0) (Printf.sprintf "mu. %s" (typ_prec 0 a))
  | TSig mt -> paren (p > 0) (modtyp_prec mt)

and modtyp_prec = function
  | TyIntf t -> typ_prec 1 t
  | TyArrM (t, mt) -> Printf.sprintf "%s => %s" (typ_prec 1 t) (modtyp_prec mt)

let typ_to_string t = typ_prec 0 t
