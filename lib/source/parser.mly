%{
open Ast

let nd (s, e) it = { it; loc = { start_p = s; end_p = e } }
let bd (s, e) name = { bd_name = name; bd_loc = { start_p = s; end_p = e } }
%}

%token <int> INT
%token <string> STRING
%token <string> IDENT
%token LET REC IN FUN IF THEN ELSE CASE OF INL INR END FOLD UNFOLD MU
%token STRUCT SANDBOX FUNCTOR MODULE OPEN TYPE WITH LINK LINKALL BOX
%token MOD NOT TRUE FALSE
%token TINT TBOOL TSTRING TTOP
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COLON SEMI SEMISEMI DOT ARROW DARROW
%token EQ NE LT LE GT GE BAR BARBAR AMP AMPAMP
%token COMMACOMMA COMMACOMMACOMMA
%token PLUS MINUS STAR SLASH CARET QUERY EOF

%start <Ast.named> program

%%

program:
  | ds = list(decl); m = option(preceded(SEMISEMI, exp)); EOF
      { { decls = ds; main = m } }

(* ---------------- declarations ---------------- *)

decl:
  | LET; b = binding
      { nd $loc (DLet b) }
  | MODULE; name = IDENT; ps = list(param); EQ; e = exp
      { let body =
          if ps = [] then e else nd $loc(e) (EFunctor (Open, ps, e))
        in
        nd $loc (DModule (bd $loc(name) name, body)) }
  | OPEN; e = exp
      { nd $loc (DOpen e) }
  | TYPE; name = IDENT; EQ; t = typ
      { nd $loc (DType (bd $loc(name) name, t)) }

binding:
  | r = boption(REC); name = IDENT; ps = list(param);
    ann = option(preceded(COLON, typ)); EQ; e = exp
      { { b_rec = r; b_bind = bd $loc(name) name;
          b_params = ps; b_ann = ann; b_exp = e } }

param:
  | LPAREN; name = IDENT; COLON; t = typ; RPAREN
      { { p_bind = bd $loc(name) name; p_typ = t } }

(* ---------------- expressions ---------------- *)

(* Lowest level: forms whose body extends as far right as possible. *)
exp:
  | LET; b = binding; IN; e = exp
      { nd $loc (ELet (b, e)) }
  | FUN; ps = nonempty_list(param); ARROW; e = exp
      { nd $loc (ELam (ps, e)) }
  | FUNCTOR; ps = nonempty_list(param); ARROW; e = exp
      { nd $loc (EFunctor (Open, ps, e)) }
  | SANDBOX; FUNCTOR; ps = nonempty_list(param); ARROW; e = exp
      { nd $loc (EFunctor (Sandboxed, ps, e)) }
  | IF; c = merge_exp; THEN; t = exp; ELSE; f = exp
      { nd $loc (EIf (c, t, f)) }
  | OPEN; m = merge_exp; IN; e = exp
      { nd $loc (EOpen (m, e)) }
  | BOX; m = merge_exp; IN; e = exp
      { nd $loc (EBox (m, e)) }
  | LINK; m = merge_exp; WITH; f = exp
      { nd $loc (ELink (LOne, m, f)) }
  | LINKALL; m = merge_exp; WITH; f = exp
      { nd $loc (ELink (LAll, m, f)) }
  | e = merge_exp
      { e }

merge_exp:
  | l = merge_exp; COMMACOMMA; r = or_exp
      { nd $loc (EMerge (MNon, l, r)) }
  | l = merge_exp; COMMACOMMACOMMA; r = or_exp
      { nd $loc (EMerge (MDep, l, r)) }
  | e = or_exp
      { e }

or_exp:
  | l = and_exp; BARBAR; r = or_exp   { nd $loc (EBinop (Or, l, r)) }
  | e = and_exp                       { e }

and_exp:
  | l = cmp_exp; AMPAMP; r = and_exp  { nd $loc (EBinop (And, l, r)) }
  | e = cmp_exp                       { e }

cmp_exp:
  | l = cmp_exp; op = cmp_op; r = cat_exp { nd $loc (EBinop (op, l, r)) }
  | e = cat_exp                           { e }

%inline cmp_op:
  | EQ { Eq } | NE { Ne } | LT { Lt } | LE { Le } | GT { Gt } | GE { Ge }

cat_exp:
  | l = add_exp; CARET; r = cat_exp   { nd $loc (EBinop (Cat, l, r)) }
  | e = add_exp                       { e }

add_exp:
  | l = add_exp; PLUS;  r = mul_exp   { nd $loc (EBinop (Add, l, r)) }
  | l = add_exp; MINUS; r = mul_exp   { nd $loc (EBinop (Sub, l, r)) }
  | e = mul_exp                       { e }

mul_exp:
  | l = mul_exp; STAR;  r = un_exp    { nd $loc (EBinop (Mul, l, r)) }
  | l = mul_exp; SLASH; r = un_exp    { nd $loc (EBinop (Div, l, r)) }
  | l = mul_exp; MOD;   r = un_exp    { nd $loc (EBinop (Mod, l, r)) }
  | e = un_exp                        { e }

un_exp:
  | MINUS; e = un_exp                 { nd $loc (EUnop (Neg, e)) }
  | NOT;   e = un_exp                 { nd $loc (EUnop (Not, e)) }
  | e = app_exp                       { e }

(* The injection and (un)fold markers take an atom, so `inl f x` is
   `(inl f) x` — never ambiguous, at the cost of parenthesising `inl (f x)`. *)
app_exp:
  | f = app_exp; a = atom             { nd $loc (EApp (f, a)) }
  | INL;    a = atom                  { nd $loc (EInl a) }
  | INR;    a = atom                  { nd $loc (EInr a) }
  | FOLD;   a = atom                  { nd $loc (EFold a) }
  | UNFOLD; a = atom                  { nd $loc (EUnfold a) }
  | e = atom                          { e }

atom:
  | x = IDENT                         { nd $loc (EVar x) }
  | n = INT                           { nd $loc (ELit (LInt n)) }
  | s = STRING                        { nd $loc (ELit (LString s)) }
  | TRUE                              { nd $loc (ELit (LBool true)) }
  | FALSE                             { nd $loc (ELit (LBool false)) }
  | QUERY                             { nd $loc EQuery }
  | LPAREN; RPAREN                    { nd $loc EUnit }
  | LPAREN; e = exp; RPAREN           { nd $loc e.it }
  | LPAREN; e = exp; COLON; t = typ; RPAREN
      { nd $loc (EAnnot (e, t)) }
  | LBRACE; fs = separated_list(SEMI, field); RBRACE
      { nd $loc (ERcd fs) }
  | a = atom; DOT; l = IDENT          { nd $loc (EField (a, l)) }
  | a = atom; DOT; LBRACKET; n = INT; RBRACKET
      { nd $loc (EIndex (a, n)) }
  | STRUCT; ds = list(decl); END      { nd $loc (EStruct (Open, ds)) }
  | SANDBOX; STRUCT; ds = list(decl); END
      { nd $loc (EStruct (Sandboxed, ds)) }
  | CASE; scrut = exp; OF; option(BAR);
    INL; x = IDENT; ARROW; e1 = exp;
    BAR; INR; y = IDENT; ARROW; e2 = exp; END
      { nd $loc (ECase (scrut, bd $loc(x) x, e1, bd $loc(y) y, e2)) }

field:
  | l = IDENT; EQ; e = exp            { (l, e) }

(* ---------------- types ---------------- *)

typ:
  | MU; a = IDENT; DOT; t = typ       { nd $loc (TMu (bd $loc(a) a, t)) }
  | l = arrow_typ; DARROW; r = typ    { nd $loc (TSig (l, r)) }
  | t = arrow_typ                     { t }

arrow_typ:
  | l = or_typ; ARROW; r = arrow_typ  { nd $loc (TArr (l, r)) }
  | t = or_typ                        { t }

or_typ:
  | l = or_typ; BAR; r = and_typ      { nd $loc (TOr (l, r)) }
  | t = and_typ                       { t }

and_typ:
  | l = and_typ; AMP; r = atom_typ    { nd $loc (TAnd (l, r)) }
  | t = atom_typ                      { t }

atom_typ:
  | TINT                              { nd $loc TInt }
  | TBOOL                             { nd $loc TBool }
  | TSTRING                           { nd $loc TString }
  | TTOP                              { nd $loc TTop }
  | a = IDENT                         { nd $loc (TVar a) }
  | LBRACE; fs = separated_list(SEMI, typ_field); RBRACE
      { nd $loc (TRcd fs) }
  | LPAREN; t = typ; RPAREN           { nd $loc t.it }

typ_field:
  | l = IDENT; COLON; t = typ         { (l, t) }
