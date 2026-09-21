(* AST for core λSCE (Source language core) 
  Parametric on the variable representation:
  - De-bruijn/Nameless vs. Named
*)

type typ =
  | TInt
  | TBool
  | TString
  | TTop
  | TArr of typ * typ
  | TAnd of typ * typ
  | TOr  of typ * typ
  | TRcd of string * typ
  (* module types: Sig A classifies structures, A => B functors *)
  | TSig  of typ
  | TMarr of typ * typ
  (* iso-recursive types: de Bruijn var 0 is bound by the nearest mu *)
  | TVar of int
  | TMu  of typ

(* subst_typ d s t replaces TVar d by s in t (s is closed, so no shifting) *)
let rec subst_typ d s = function
  | TInt        -> TInt
  | TBool       -> TBool
  | TString     -> TString
  | TTop        -> TTop
  | TArr (a, b) -> TArr (subst_typ d s a, subst_typ d s b)
  | TAnd (a, b) -> TAnd (subst_typ d s a, subst_typ d s b)
  | TOr  (a, b) -> TOr  (subst_typ d s a, subst_typ d s b)
  | TRcd (l, a) -> TRcd (l, subst_typ d s a)
  | TSig a      -> TSig (subst_typ d s a)
  | TMarr (a, b) -> TMarr (subst_typ d s a, subst_typ d s b)
  | TVar n      -> if n = d then s else TVar n
  | TMu t       -> TMu (subst_typ (d + 1) s t)

type sandbox =
  | Sandboxed
  | Open

type lit =
  | Int    of int
  | Bool   of bool
  | String of string

(* primitive operators; surface `&&`, `||`, `not` and unary `-` desugar away *)
type binop =
  | Add | Sub | Mul | Div | Mod   (* Int -> Int -> Int *)
  | Lt  | Le  | Gt  | Ge          (* Int -> Int -> Bool *)
  | Eq  | Ne                      (* A -> A -> Bool, A primitive *)
  | Cat                           (* String -> String -> String *)

type binder = string
let anon : binder = "_"
type void = |

type 'v exp =
  | Var       of 'v (* named only; Debruijn turns it into Proj (Query, i) *)
  | Query
  | Proj      of 'v exp * int
  | Lit       of lit
  | Unit
  | Lam       of binder * typ * 'v exp
  | Box       of 'v exp * 'v exp
  | Clos      of 'v exp * typ * 'v exp
  | App       of 'v exp * 'v exp
  | Mrg       of binder * 'v exp * 'v exp
  | Lrec      of string * 'v exp
  | Rproj     of 'v exp * string
  (* primitives *)
  | Binop     of binop * 'v exp * 'v exp
  | If        of 'v exp * 'v exp * 'v exp
  (* to be elaborated *)
  | Mstruct   of 'v exp
  | Mfunctor  of sandbox * binder * typ * 'v exp
  | Mclos     of 'v exp * typ * 'v exp
  | Mlink     of 'v exp * 'v exp
  | Mapp      of 'v exp * 'v exp
  (* more terms *)
  | Nmrg      of 'v exp * 'v exp                    (* binds nothing: see Frames.nmrg *)
  | Letb      of binder * 'v exp * 'v exp
  | Openm     of binder * 'v exp * 'v exp
  (* n-ary linking: satisfy every labeled import of a functor at once *)
  | Mlinkn    of 'v exp * 'v exp
  (* unions: Inl (B, e) injects into _ ∨ B, Inr (A, e) into A ∨ _ *)
  | Inl       of typ * 'v exp
  | Inr       of typ * 'v exp
  | Case      of 'v exp * binder * 'v exp * binder * 'v exp
  (* fixpoint: Flam (f, x, A, B, e) is a recursive function of type A → B;
     its body sees ?.0 = the argument x, ?.1 = the function itself f *)
  | Flam      of binder * binder * typ * typ * 'v exp
  | Fclos     of 'v exp * typ * typ * 'v exp
  (* iso-recursive types: Fold (T, e) stores the mu-body T, folds into mu T *)
  | Fold      of typ * 'v exp
  | Unfold    of 'v exp

type named    = string exp
type nameless = void exp

(* Value judgment from the Lean `Value : Exp → Prop` inductive *)
let rec is_value : 'v. 'v exp -> bool = function
  | Lit _ | Unit       -> true
  | Clos  (v, _, _)    -> is_value v
  | Mclos (v, _, _)    -> is_value v
  | Mstruct v          -> is_value v
  | Mrg   (_, v1, v2)  -> is_value v1 && is_value v2
  | Lrec  (_, v)       -> is_value v
  | Inl (_, v) | Inr (_, v) -> is_value v
  | Fclos (v, _, _, _)      -> is_value v
  | Fold  (_, v)    -> is_value v
  | _               -> false
