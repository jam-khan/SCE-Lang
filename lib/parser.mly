%token <int> INT
%token PLUS MINUS TIMES DIV
%token LPAREN RPAREN
%token EOF

%left PLUS MINUS
%left TIMES DIV

%start <Ast.expr> program

%%

program:
  | e = expr; EOF { e }

expr:
  | n = INT                      { Ast.Int n }
  | LPAREN; e = expr; RPAREN     { e }
  | lhs = expr; PLUS;  rhs = expr { Ast.Binop (Ast.Add, lhs, rhs) }
  | lhs = expr; MINUS; rhs = expr { Ast.Binop (Ast.Sub, lhs, rhs) }
  | lhs = expr; TIMES; rhs = expr { Ast.Binop (Ast.Mul, lhs, rhs) }
  | lhs = expr; DIV;   rhs = expr { Ast.Binop (Ast.Div, lhs, rhs) }
