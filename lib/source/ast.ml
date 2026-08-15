(* Surface AST (full sugar and direct from parsing) *)

(*
  Lexing.position is a record from Lexing module

  type position = {
    pos_fname : string; -- file name
    pos_lnum  : int;    -- line number, 1-based
    pos_bol   : int;    -- byte offset of the start of this line
    pos_cnum  : int;    -- byte offset of this position, 0-based
  }
  
  This is useful for error messages, so we can report the location.
*)
type loc = { start_p : Lexing.position; end_p : Lexing.position }

type 'a node = { it  : 'a; loc : loc }

let mk loc it = { it; loc }

(* For synthesized nodes. Lexing.dummy_pos is line 0 / offset -1, deliberately
   invalid, so it cannot be confused with the start of a real file. Driver.render
   must guard on it (line < 1 || col < 0) and drop the location — the negative
   offset otherwise raises from List.nth_opt and String.make. *)
let dummy_loc = { start_p = Lexing.dummy_pos; end_p = Lexing.dummy_pos }

(* A resolved variable occurrence. λSCE has no variables: `PIdx i` becomes
   `Proj (Query, i)` and `PField (i, l)` becomes `Rproj (Proj (Query, i), l)`. *)
type path =
  | PIdx    of int
  | PField  of int * string

type binder = { bd_name : string; bd_loc : loc }

(* types *)

type 'tv typ = 'tv typ_desc node

and 'tv typ_desc =
  | TInt
  | TBool
  | TString
  | TTop
  (* 'tv is string when named, and int when de-bruijn/nameless *)
  | TVar of 'tv
  | TArr of 'tv typ * 'tv typ
  | TAnd of 'tv typ * 'tv typ
  | TOr  of 'tv typ * 'tv typ
  | TRcd of (string * 'tv typ) list    (* { l : A, ... } *)
  | TMu  of binder  * 'tv typ
  | TSig of 'tv typ * 'tv typ

type 'tv param = { p_bind : binder; p_typ : 'tv typ }

(* expressions *)

(* literals : int, bool, strings *)
type lit =
  | LInt    of int
  | LBool   of bool
  | LString of string

(* primitive binary ops. `And`/`Or` are surface-only: they are eliminated into
   `EIf` by the desugarer, not by the parser, so errors can point at the
   operator the user wrote. *)
type binop =
  | Add | Sub | Mul | Div | Mod
  | Lt  | Le  | Gt  | Ge
  | Eq  | Ne
  | Cat
  | And | Or

type unop = Neg | Not

type merge_kind 
  = MNon        (* Non-dependent merge:  ;  = Nmrg *)
  | MDep        (* Dependent merge:      ;; = Mrg  *)

type link_kind = LOne | LAll

type sandbox = Sandboxed | Open

type ('v, 'tv) exp = ('v, 'tv) exp_desc node

and ('v, 'tv) exp_desc =
  | EVar     of 'v
  | ELit     of lit
  | EUnit
  | EAnnot   of ('v, 'tv) exp * 'tv typ                (* (e : A) *)
  | EBinop   of binop * ('v, 'tv) exp * ('v, 'tv) exp
  | EUnop    of unop * ('v, 'tv) exp
  | EIf      of ('v, 'tv) exp * ('v, 'tv) exp * ('v, 'tv) exp
  | ELam     of 'tv param list * ('v, 'tv) exp
  | EApp     of ('v, 'tv) exp * ('v, 'tv) exp
  | ERcd     of (string * ('v, 'tv) exp) list          (* { l = e, ... } *)
  | EField   of ('v, 'tv) exp * string                 (* e.l *)
  | EMerge   of merge_kind * ('v, 'tv) exp * ('v, 'tv) exp
  | ELet     of ('v, 'tv) binding * ('v, 'tv) exp
  | EOpen    of ('v, 'tv) exp * ('v, 'tv) exp          (* open e in e *)
  | EInl     of ('v, 'tv) exp
  | EInr     of ('v, 'tv) exp
  | ECase    of ('v, 'tv) exp * binder * ('v, 'tv) exp * binder * ('v, 'tv) exp
  | EFold    of ('v, 'tv) exp
  | EUnfold  of ('v, 'tv) exp
  | EStruct  of sandbox * ('v, 'tv) decl list
  | EFunctor of sandbox * 'tv param list * ('v, 'tv) exp
  | ELink    of link_kind * ('v, 'tv) exp * ('v, 'tv) exp
  (* ADT sugar, eliminated by Adt.expand before resolution:
     match e with | C x -> e | C (x, y) -> e | _ -> e end *)
  | EMatch   of ('v, 'tv) exp * (binder * binder list * ('v, 'tv) exp) list
  (* escape hatches onto the raw calculus *)
  | EQuery                                             (* ? *)
  | EIndex   of ('v, 'tv) exp * int                    (* e.[n] *)
  | EBox     of ('v, 'tv) exp * ('v, 'tv) exp          (* box e in e *)

and ('v, 'tv) binding = {
  b_rec     : bool;
  b_bind    : binder;
  b_params  : 'tv param list;
  b_ann     : 'tv typ option;
  b_exp     : ('v, 'tv) exp;
}

and ('v, 'tv) decl = ('v, 'tv) decl_desc node

and ('v, 'tv) decl_desc =
  | DLet    of ('v, 'tv) binding
  | DModule of binder * ('v, 'tv) exp
  | DOpen   of ('v, 'tv) exp
  | DType   of binder * 'tv typ
  (* ADT sugar *)
  | DAdt    of binder * (binder * 'tv typ list) list

type 'tv import_source =
  | IAuto
  | IFile   of string
  | IInline of 'tv typ

(* `main` is never set by the parser — a program is its `let main` declaration.
   The field survives because Sepcomp.unit_wrapper synthesizes one when it wraps
   a unit's declarations as a sandboxed functor. *)
type ('v, 'tv) program = {
  imports : (binder * 'tv import_source) list;
  decls   : ('v, 'tv) decl list;
  main    : ('v, 'tv) exp option;
}

(* A parsed .scei interface file: type aliases, then the interface type *)
type 'tv intf = { i_aliases : (binder * 'tv typ) list; i_typ : 'tv typ }

(* Named instance of AST *)
type named = (string, string) program

(* Nameless/deBruijn instance of AST *)
type indexed = (path, int) program

(* ---- misc ---- *)

let name_of_decl (d : ('v, 'tv) decl) : string option =
  match d.it with
  | DLet b -> Some b.b_bind.bd_name
  | DModule (b, _) -> Some b.bd_name
  | DType _ | DOpen _ | DAdt _ -> None

let string_of_binop = function
  | Add -> "+"  | Sub -> "-"  | Mul -> "*" | Div -> "/" | Mod -> "mod"
  | Lt  -> "<"  | Le  -> "<=" | Gt  -> ">" | Ge -> ">="
  | Eq  -> "="  | Ne  -> "<>" | Cat -> "^"
  | And -> "&&" | Or  -> "||"

let string_of_unop = function Neg -> "-" | Not -> "not"