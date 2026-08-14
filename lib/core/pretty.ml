(* Printers for λE types and values. *)
open Ast

(* Precedence levels, loosest first: 0 arrow, 1 union, 2 intersection, 3 atom. *)
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

let typ_to_string t = typ_prec 0 t

let lit_to_string = function
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | String s -> Printf.sprintf "%S" s

let string_of_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "mod"
  | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
  | Eq -> "=" | Ne -> "<>" | Cat -> "^"

(* A merge whose whole spine is labelled prints as a record, which is how the
   surface language wrote it in the first place. *)
let rec record_fields = function
  | Lrec (l, v) -> Some [ (l, v) ]
  | Mrg (v1, v2) -> (
    match (record_fields v1, record_fields v2) with
    | Some f1, Some f2 -> Some (f1 @ f2)
    | _ -> None)
  | _ -> None

let rec exp_to_string e =
  match record_fields e with
  | Some fields when fields <> [] ->
    "{ "
    ^ String.concat ", "
        (List.map (fun (l, v) -> Printf.sprintf "%s = %s" l (exp_to_string v)) fields)
    ^ " }"
  | _ -> (
    match e with
    | Lit l -> lit_to_string l
    | Unit -> "()"
    | Query -> "?"
    | Proj (e1, n) -> Printf.sprintf "%s.[%d]" (exp_to_string e1) n
    | Lrec (l, e1) -> Printf.sprintf "{ %s = %s }" l (exp_to_string e1)
    | Rproj (e1, l) -> Printf.sprintf "%s.%s" (exp_to_string e1) l
    | Mrg (a, b) -> Printf.sprintf "(%s ; %s)" (exp_to_string a) (exp_to_string b)
    | Binop (op, a, b) ->
      Printf.sprintf "(%s %s %s)" (exp_to_string a) (string_of_binop op)
        (exp_to_string b)
    | If (c, t, f) ->
      Printf.sprintf "(if %s then %s else %s)" (exp_to_string c)
        (exp_to_string t) (exp_to_string f)
    | Inl (_, e1) -> Printf.sprintf "inl %s" (exp_to_string e1)
    | Inr (_, e1) -> Printf.sprintf "inr %s" (exp_to_string e1)
    | Fold (_, e1) -> Printf.sprintf "fold %s" (exp_to_string e1)
    | Unfold e1 -> Printf.sprintf "unfold %s" (exp_to_string e1)
    | Hostfn (n, _, _) -> Printf.sprintf "<host %s>" n
    | Lam (a, _) | Clos (_, a, _) -> Printf.sprintf "<fun : %s -> _>" (typ_to_string a)
    | Flam (a, b, _) | Fclos (_, a, b, _) ->
      Printf.sprintf "<rec fun : %s -> %s>" (typ_to_string a) (typ_to_string b)
    | App (a, b) -> Printf.sprintf "(%s %s)" (exp_to_string a) (exp_to_string b)
    | Box (a, b) -> Printf.sprintf "(box %s in %s)" (exp_to_string a) (exp_to_string b)
    | Case (s, _, _) -> Printf.sprintf "(case %s ...)" (exp_to_string s))
