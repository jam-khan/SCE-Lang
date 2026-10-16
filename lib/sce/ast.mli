(** Source-core syntax, parameterized by the representation of term variables. *)

(** [TVar 0] is bound by the nearest enclosing [TMu]. [TSig] classifies
    structures; [TMarr] classifies module functors. *)
type typ =
  | TInt
  | TBool
  | TString
  | TTop
  | TArr of typ * typ
  | TAnd of typ * typ
  | TOr of typ * typ
  | TRcd of string * typ
  | TSig of typ
  | TMarr of typ * typ
  | TVar of int
  | TMu of typ

(** [subst_typ d replacement t] replaces index [d], increasing the target
    index under each [TMu]. [replacement] must be closed: no shifting or
    renumbering of other free variables is performed. *)
val subst_typ : int -> typ -> typ -> typ

type sandbox =
  | Sandboxed (** A functor captures the empty environment. *)
  | Open (** A functor captures the ambient environment. *)

type lit =
  | Int of int
  | Bool of bool
  | String of string

(** Arithmetic and ordering use integers; equality uses matching primitive
    types; [Cat] concatenates strings. *)
type binop =
  | Add | Sub | Mul | Div | Mod
  | Lt | Le | Gt | Ge
  | Eq | Ne
  | Cat

type binder = string

(** The conventional anonymous binder, ["_"]. *)
val anon : binder

(** An empty type rules out [Var] in resolved terms. *)
type void = |

(** [Query] denotes the complete environment. Index zero selects the right
    component of a merge; higher indices follow the left spine, excluding
    its terminal base. Runtime environments conventionally start at [Unit].
    Binder names are retained after resolution but evaluation ignores them. *)
type 'v exp =
  | Var of 'v
  | Query
  | Proj of 'v exp * int
  | Lit of lit
  | Unit
  | Lam of binder * typ * 'v exp
  | Box of 'v exp * 'v exp
      (** The first expression's value replaces the ambient environment. *)
  | Clos of 'v exp * typ * 'v exp
      (** Captured value environment, argument type, body. *)
  | App of 'v exp * 'v exp
  | Mrg of binder * 'v exp * 'v exp
      (** Its right operand sees the left value as one new binding. *)
  | Lrec of string * 'v exp
  | Rproj of 'v exp * string
  | Binop of binop * 'v exp * 'v exp
  | If of 'v exp * 'v exp * 'v exp
  | Mstruct of 'v exp
  | Mfunctor of sandbox * binder * typ * 'v exp
  | Mclos of 'v exp * typ * 'v exp
      (** Module closure with a captured value environment. *)
  | Mlink of 'v exp * 'v exp
      (** Link a provider to a functor with one labelled import. *)
  | Mapp of 'v exp * 'v exp
  | Nmrg of 'v exp * 'v exp
      (** Both operands run in the same ambient environment. *)
  | Letb of binder * 'v exp * 'v exp
  | Openm of binder * 'v exp * 'v exp
      (** Bind a single labelled record's payload in the body. *)
  | Mlinkn of 'v exp * 'v exp
      (** Link every labelled import of a functor from a provider. *)
  | Inl of typ * 'v exp
      (** The annotation is the other, right summand. *)
  | Inr of typ * 'v exp
      (** The annotation is the other, left summand. *)
  | Case of 'v exp * binder * 'v exp * binder * 'v exp
      (** Each branch binds its injection payload at index zero. *)
  | Flam of binder * binder * typ * typ * 'v exp
      (** Recursive name, argument name, argument type, result type, body.
          The body sees the argument at index zero and itself at index one. *)
  | Fclos of 'v exp * typ * typ * 'v exp
      (** Recursive closure with a captured value environment. *)
  | Fold of typ * 'v exp
      (** [Fold (body, e)] has type [TMu body]; the annotation is the mu body. *)
  | Unfold of 'v exp

type named = string exp
type nameless = void exp

(** The runtime value predicate, including recursively valued environments
    and payloads. It does not check types or closure bodies. *)
val is_value : 'v exp -> bool
