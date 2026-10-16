(** Syntax and runtime values of the explicit-environment core calculus. *)

(** Recursive type variables use de Bruijn indices: [TVar 0] denotes the
    nearest enclosing [TMu]. Whole types should be closed; [Fold] stores only
    a mu body. *)
type typ =
  | TInt
  | TBool
  | TString
  | TTop
  | TArr of typ * typ
  | TAnd of typ * typ
  | TOr of typ * typ
  | TRcd of string * typ
  | TVar of int
  | TMu of typ

type lit =
  | Int of int
  | Bool of bool
  | String of string

(** Equality accepts matching primitive types; arithmetic and ordering use
    integers, and [Cat] concatenates strings. *)
type binop =
  | Add | Sub | Mul | Div | Mod
  | Lt | Le | Gt | Ge
  | Eq | Ne
  | Cat

(** Environments are values, conventionally a left-associated [Mrg] chain
    rooted at [Unit]. [Query] denotes the whole environment. Positional index
    zero selects the right component of a merge; further indices follow its
    left spine, never selecting the terminal base itself. *)
type exp =
  | Query
  | Proj of exp * int
  | Lit of lit
  | Unit
  | Lam of typ * exp
      (** The body runs with the argument appended to the captured environment. *)
  | Box of exp * exp
      (** Evaluate the second expression under the first expression's value. *)
  | Clos of exp * typ * exp
      (** Captured environment, argument type, body; the environment is a value. *)
  | App of exp * exp
  | Mrg of exp * exp
      (** The right operand sees the left operand's value appended to its
          ambient environment. *)
  | Lrec of string * exp
  | Rproj of exp * string
  | Binop of binop * exp * exp
  | If of exp * exp * exp
  | Inl of typ * exp
      (** [Inl (b, e)] supplies the other summand [b]. *)
  | Inr of typ * exp
      (** [Inr (a, e)] supplies the other summand [a]. *)
  | Case of exp * exp * exp
      (** Each branch receives the injection payload at index zero. *)
  | Flam of typ * typ * exp
      (** Argument type, result type, body. The body sees its argument at
          index zero and the recursive function at index one. *)
  | Fclos of exp * typ * typ * exp
      (** Recursive closure with a captured value environment. *)
  | Fold of typ * exp
      (** [Fold (body, e)] has type [TMu body]; the annotation is the mu body. *)
  | Unfold of exp
  | Hostfn of string * typ * typ
      (** Host capability name, argument type, result type. Application uses
          {!Eval.host_dispatch}; the annotation does not validate the host code. *)

(** The runtime value predicate, including recursively valued environments
    and payloads. It does not check types or closure bodies. *)
val is_value : exp -> bool
