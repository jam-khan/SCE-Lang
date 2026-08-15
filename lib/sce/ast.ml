(* AST for core λSCE (Source language core) *)

type typ =
  | TInt
  | TBool
  | TString
  | TTop
  | TArr of typ * typ
  | TAnd of typ * typ
  | TOr  of typ * typ
  | TRcd of string * typ
  | TSig of modtyp
  (* iso-recursive types: de Bruijn var 0 is bound by the nearest mu *)
  | TVar of int
  | TMu  of typ

and modtyp =
  | TyIntf of typ
  | TyArrM of typ * modtyp

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
  | TSig mt     -> TSig (subst_modtyp d s mt)
  | TVar n      -> if n = d then s else TVar n
  | TMu t       -> TMu (subst_typ (d + 1) s t)

and subst_modtyp d s = function
  | TyIntf t       -> TyIntf (subst_typ d s t)
  | TyArrM (t, mt) -> TyArrM (subst_typ d s t, subst_modtyp d s mt)

type sandbox =
  | Sandboxed
  | Open

type lit =
  | Int    of int
  | Bool   of bool
  | String of string

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
  (* to be elaborated *)
  | Mstruct  of sandbox * exp
  | Mfunctor of sandbox * typ * exp
  | Mclos    of exp * typ * exp
  | Mlink    of exp * exp
  | Mapp     of exp * exp
  (* more terms *)
  | Nmrg  of exp * exp
  | Letb  of exp * typ * exp
  | Openm of exp * exp
  (* n-ary linking: satisfy every labeled import of a functor at once *)
  | Mlinkn of exp * exp
  (* unions: Inl (B, e) injects into _ ∨ B, Inr (A, e) into A ∨ _ *)
  | Inl  of typ * exp
  | Inr  of typ * exp
  | Case of exp * exp * exp
  (* fixpoint: Flam (A, B, e) is a recursive function of type A → B;
     its body sees ?.0 = argument, ?.1 = the function itself *)
  | Flam  of typ * typ * exp
  | Fclos of exp * typ * typ * exp
  (* iso-recursive types: Fold (T, e) stores the mu-body T, folds into mu T *)
  | Fold   of typ * exp
  | Unfold of exp

(* Value judgment from the Lean `Value : Exp → Prop` inductive *)
let rec is_value = function
  | Lit _ | Unit    -> true
  | Clos  (v, _, _) -> is_value v
  | Mclos (v, _, _) -> is_value v
  | Mrg   (v1, v2)  -> is_value v1 && is_value v2
  | Lrec  (_, v)    -> is_value v
  | Inl (_, v) | Inr (_, v) -> is_value v
  | Fclos (v, _, _, _)      -> is_value v
  | Fold  (_, v)    -> is_value v
  | _               -> false
