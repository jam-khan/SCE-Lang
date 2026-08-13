%{
open Ast

(* Takes an AST, wraps it with start line `s` and end line `e` *)
let nd (s, e) it = { it; loc = { start_p = s; end_p = e } }

(* Takes a binder name, and wraps it with the start line `s` and end line `e` *)
let bd (s, e) name = { bd_name = name; bd_loc = { start_p = s; end_p = e } }

%}

(* Tokens *)
%token <int>    INT
%token <string> STRING
%token <string> IDENT
%token LET REC IN FUN IF THEN ELSE CASE OF INL INR END FOLD UNFOLD MU
%token STRUCT SANDBOX FUNCTOR MODULE OPEN TYPE WITH LINK LINKALL BOX IMPORT
%token MATCH MOD NOT TRUE FALSE
%token TINT TBOOL TSTRING TTOP
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COLON SEMI SEMISEMI DOT ARROW DARROW
%token EQ NE LT LE GT GE BAR BARBAR AMP AMPAMP
%token COMMA COMMACOMMA COMMACOMMACOMMA
%token PLUS MINUS START SLASH CARET QUERY EOF

%start <Ast.named> program
%start <string Ast.intf> intf_file

%%

(* Program Grammar rules *)

program :
  | is = list(import_decl); ds = list(decl); m = option(preceded(SEMISEMI, exp)); EOF
        { 
          { imports = is; 
            decls   = ds; 
            main = m 
          } 
        }

(**
    Top level import declaration

    Examples
    1) import foo           this leads to `ann = None`, so src = IAuto
    2) import foo : Bar     this leads to `ann = .. TVar a; ..`, so src = IFile a
    3) import foo : TYPE    this leads to the actual type `t` inlined.
**)
import_decl:
  | IMPORT; name = IDENT; ann = option(preceded(COLON, typ))
      { let src =
          match ann with
          | None                    -> IAuto
          | Some { it = TVar a; _}  -> IFile a
          | Some t                  -> IInline t
        in
        (bd $loc(name) name, src) }