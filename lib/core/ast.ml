(* AST for core λE with extensions. *)

type typ =
  | TInt
  | TBool
  | TString
  | TTop
  | TArr of typ * typ
  | TAnd of typ * typ
  | TOr of typ * typ
  | TRcd of string * typ
  (* iso-recursive types: de Bruijn var 0 is bound by the nearest mu *)
  | TVar of int
  | TMu of typ

type lit =
  | Int     of int
  | Bool    of bool
  | String  of string

(* Primitive Operators *)

(* primitive operators; surface `&&`, `||`, `not` and unary `-` desugar away *)
type binop =
  | Add | Sub | Mul | Div | Mod   (* Int -> Int -> Int *)
  | Lt  | Le  | Gt  | Ge          (* Int -> Int -> Bool *)
  | Eq  | Ne                      (* A -> A -> Bool, A primitive *)
  | Cat                           (* String -> String -> String *)

type exp =
  | Query
  | Proj  of exp * int
  | Lit   of lit
  | Unit
  | Lam   of typ * exp
  | Box   of exp * exp
  | Clos  of exp * typ * exp
  | App   of exp * exp
  | Mrg   of exp * exp
  | Lrec  of string * exp
  | Rproj of exp * string
  (* primitives *)
  | Binop of binop * exp * exp
  | If    of exp   * exp * exp
  (* unions: Inl (B, e) injects into _ ∨ B, Inr (A, e) into A ∨ _ *)
  | Inl   of typ * exp
  | Inr   of typ * exp
  | Case  of exp * exp * exp
  (* fixpoint: Flam (A, B, e) is a recursive function of type A → B;
     its body sees ?.0 = argument, ?.1 = the function itself *)
  | Flam  of typ * typ * exp
  | Fclos of exp * typ * typ * exp
  (* iso-recursive types: Fold (T, e) stores the mu-body T, folds into mu T *)
  | Fold    of typ * exp
  | Unfold  of exp
  (* a host capability: applied like a function, dispatched by name through
     Eval.host_dispatch; only host-built provider units contain these *)
  | Hostfn  of string * typ * typ

(* Value judgment from the Lean `Value : Exp → Prop` inductive *)
let rec is_value = 
  function
    | Lit _ | Unit   -> true
    | Clos (v, _, _) -> is_value v
    | Lrec (_, v)    -> is_value v
    | Mrg  (v1, v2)  -> is_value v1 && is_value v2
    | Inl  (_, v) | Inr (_, v) -> is_value v
    | Fclos (v, _, _, _)       -> is_value v
    | Fold (_, v)    -> is_value v
    | Hostfn _       -> true
    | _              -> false
