(* Surface AST (full sugar and direct from parsing).

   Names stay names here. Sugar resolves them against the types it synthesizes,
   on the way down to λSCE, and it is the λSCE tree that then loses them
   (lib/sce/debruijn.ml) — so there is only one surface tree, the one the parser
   builds. *)

type loc = { start_p : Lexing.position; end_p : Lexing.position }

type 'a node = { it : 'a; loc : loc }

let mk loc it = { it; loc }

(* For synthesized nodes. Lexing.dummy_pos is line 0 / offset -1, deliberately
   invalid, so it cannot be confused with the start of a real file; Driver.render
   detects it and drops the location rather than pointing at line 1. *)
let dummy_loc = { start_p = Lexing.dummy_pos; end_p = Lexing.dummy_pos }

type binder = { bd_name : string; bd_loc : loc }

(* ---- types ---- *)

type typ = typ_desc node

and typ_desc =
  | TInt
  | TBool
  | TString
  | TTop
  | TVar of string                (* a mu binder or a type alias *)
  | TArr of typ * typ             (* A -> B *)
  | TAnd of typ * typ             (* A & B *)
  | TOr  of typ * typ             (* A | B *)
  | TRcd of (string * typ) list   (* { l : A; ... } *)
  | TMu  of binder * typ          (* mu a. A *)
  | TSig of typ * typ             (* A => B, a functor signature *)

type param = { p_bind : binder; p_typ : typ }

(* ---- expressions ---- *)

type lit =
  | LInt    of int
  | LBool   of bool
  | LString of string

(* `And`/`Or` are surface-only: they are eliminated into `If` by the desugarer,
   not by the parser, so errors can point at the operator the user wrote. *)
type binop =
  | Add | Sub | Mul | Div | Mod
  | Lt  | Le  | Gt  | Ge
  | Eq  | Ne
  | Cat
  | And | Or

type unop = Neg | Not

type merge_kind = MNon | MDep     (* ; = Nmrg    ;; = Mrg *)

type link_kind = LOne | LAll      (* link = Mlink    linkall = Mlinkn *)

type sandbox = Sandboxed | Open

type exp = exp_desc node

and exp_desc =
  | EVar     of string
  | ELit     of lit
  | EUnit
  | EAnnot   of exp * typ                      (* (e : A) *)
  | EBinop   of binop * exp * exp
  | EUnop    of unop * exp
  | EIf      of exp * exp * exp
  | ELam     of param list * exp
  | EApp     of exp * exp
  | ERcd     of (string * exp) list            (* { l = e; ... } *)
  | EField   of exp * string                   (* e.l *)
  | EMerge   of merge_kind * exp * exp
  | ELet     of binding * exp
  | EOpen    of exp * exp                      (* open e in e *)
  | EInl     of exp
  | EInr     of exp
  | ECase    of exp * binder * exp * binder * exp
  | EFold    of exp
  | EUnfold  of exp
  | EStruct  of sandbox * decl list
  | EFunctor of sandbox * param list * exp
  | ELink    of link_kind * exp * exp
  (* ADT sugar, eliminated by Adt.expand before resolution:
     match e with | C x -> e | C (x, y) -> e | _ -> e end *)
  | EMatch   of exp * (binder * binder list * exp) list
  (* escape hatches onto the raw calculus *)
  | EQuery                                             (* ? *)
  | EIndex   of exp * int                      (* e.[n] *)
  | EBox     of exp * exp                      (* box e in e *)

and binding = {
  b_rec    : bool;
  b_bind   : binder;
  b_params : param list;
  b_ann    : typ option;
  b_exp    : exp;
}

and decl = decl_desc node

and decl_desc =
  | DLet    of binding
  | DModule of binder * exp
  | DOpen   of exp
  | DType   of binder * typ
  (* ADT sugar, rewritten to a DType alias by Adt.expand:
     type t = | C of T * T | D *)
  | DAdt    of binder * (binder * typ list) list

(* Where a unit import's interface comes from:
   `import M` (the file M.scei), `import M : name` (the file name.scei),
   or `import M : { ... }` (written inline). *)
type import_source =
  | IAuto
  | IFile of string
  | IInline of typ

type program = {
  imports : (binder * import_source) list;
  decls : decl list;
  main  : exp option;
}

(* A parsed .scei interface file: type aliases, then the interface type. *)
type intf = { i_aliases : (binder * typ) list; i_typ : typ }

(* ---- misc ---- *)

let name_of_decl (d : decl) : string option =
  match d.it with
  | DLet b -> Some b.b_bind.bd_name
  | DModule (b, _) -> Some b.bd_name
  | DType _ | DOpen _ | DAdt _ -> None

let string_of_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "mod"
  | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
  | Eq -> "=" | Ne -> "<>" | Cat -> "^"
  | And -> "&&" | Or -> "||"

let string_of_unop = function Neg -> "-" | Not -> "not"
