(** Located, named surface syntax, including forms removed by desugaring. *)

type loc = { start_p : Lexing.position; end_p : Lexing.position }

type 'a node = { it : 'a; loc : loc }

val mk : loc -> 'a -> 'a node

val dummy_loc : loc
(** Location for synthesized nodes; its positions are outside any source file. *)

type binder = { bd_name : string; bd_loc : loc }

type typ = typ_desc node

and typ_desc =
  | TInt
  | TBool
  | TString
  | TTop
  | TVar of string
  | TArr of typ * typ
  | TAnd of typ * typ
  | TOr of typ * typ
  | TRcd of (string * typ) list
  | TMu of binder * typ
  | TSig of typ
  | TMarr of typ * typ

type param = { p_bind : binder; p_typ : typ }

type lit = LInt of int | LBool of bool | LString of string

type binop =
  | Add | Sub | Mul | Div | Mod
  | Lt | Le | Gt | Ge
  | Eq | Ne
  | Cat
  | And | Or

type unop = Neg | Not

type merge_kind =
  | MNon (** Independent operands, written [;]. *)
  | MDep (** The right operand can use the left operand's fields, written [;;]. *)

type link_kind = LOne | LAll

type sandbox = Sandboxed | Open

type exp = exp_desc node

and exp_desc =
  | EVar of string
  | ELit of lit
  | EUnit
  | EAnnot of exp * typ
  | EBinop of binop * exp * exp
  | EUnop of unop * exp
  | EIf of exp * exp * exp
  | ELam of param list * exp
  | EApp of exp * exp
  | ERcd of (string * exp) list
  | EField of exp * string
  | EMerge of merge_kind * exp * exp
  | ELet of binding * exp
  | EOpen of exp * exp
  | EInl of exp
  | EInr of exp
  | ECase of exp * binder * exp * binder * exp
  | EFold of exp
  | EUnfold of exp
  | EStruct of sandbox * decl list
  | EFunctor of sandbox * param list * exp
  | ELink of link_kind * exp * exp
  | EMatch of exp * (binder * binder list * exp) list
      (** Arms contain a constructor name, payload binders and a body.
          A constructor named [_] denotes the wildcard arm. *)
  | EQuery
  | EIndex of exp * int
  | EBox of exp * exp

and binding = {
  b_rec : bool;
  b_bind : binder;
  b_params : param list;
  b_ann : typ option;
  b_exp : exp;
}

and decl = decl_desc node

and decl_desc =
  | DLet of binding
  | DModule of binder * exp
  | DOpen of exp
  | DType of binder * typ
  | DAdt of binder * (binder * typ list) list
      (** A nonempty constructor list, in declaration order. *)

type import_source =
  | IAuto
  | IFile of string
  | IInline of typ

type program = {
  imports : (binder * import_source) list;
  decls : decl list;
  main : exp option;
      (** An optional synthesized result expression. The parser leaves this
          unset; a source entry point is a declaration named [main]. *)
}

type intf = { i_aliases : (binder * typ) list; i_typ : typ }
(** A [.scei] file: ordered type aliases followed by its interface type. *)

val name_of_decl : decl -> string option
(** The name bound by a value or module declaration; other declarations have
    no exported value name. *)

val decl_labels : decl list -> (string * loc) list
(** Value and module names with declaration locations, in source order.
    Duplicates are retained. *)

val string_of_binop : binop -> string
val string_of_unop : unop -> string
