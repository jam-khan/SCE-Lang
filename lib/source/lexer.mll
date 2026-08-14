{
open Parser

exception Error of string * Lexing.position

let error lexbuf msg = raise (Error (msg, Lexing.lexeme_start_p lexbuf))

let keywords = [
  "let", LET; "rec", REC; "in", IN; "fun", FUN;
  "if", IF; "then", THEN; "else", ELSE;
  "case", CASE; "of", OF; "inl", INL; "inr", INR; "end", END;
  "fold", FOLD; "unfold", UNFOLD; "mu", MU;
  "struct", STRUCT; "sandbox", SANDBOX; "functor", FUNCTOR; "module", MODULE;
  "open", OPEN; "type", TYPE; "with", WITH; "import", IMPORT; "match", MATCH;
  "link", LINK; "linkall", LINKALL; "box", BOX;
  "mod", MOD; "not", NOT; "true", TRUE; "false", FALSE;
  "Int", TINT; "Bool", TBOOL; "String", TSTRING; "Top", TTOP;
]

let ident_or_keyword s =
  match List.assoc_opt s keywords with Some t -> t | None -> IDENT s

let string_buf = Buffer.create 64
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha | '_') (alpha | digit | '_' | '\'')*
let white = [' ' '\t' '\r']+

rule token = parse
  | white           { token lexbuf }
  | '\n'            { Lexing.new_line lexbuf; token lexbuf }
  | "(*"            { comment 0 lexbuf }
  | digit+ as n     { INT (int_of_string n) }
  | ident as s      { ident_or_keyword s }
  (* The sub-lexer overwrites lex_start_p, so the token would otherwise be
     reported at the closing quote instead of the opening one. *)
  | '"'             { Buffer.clear string_buf;
                      let start = lexbuf.Lexing.lex_start_p in
                      let s = string_lit lexbuf in
                      lexbuf.Lexing.lex_start_p <- start;
                      STRING s }
  (* multi-character symbols must precede their prefixes *)
  | ','             { COMMA }
  | ";;"            { SEMISEMI }
  | "->"            { ARROW }
  | "=>"            { DARROW }
  | "<="            { LE }
  | "<>"            { NE }
  | ">="            { GE }
  | "&&"            { AMPAMP }
  | "||"            { BARBAR }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | '{'             { LBRACE }
  | '}'             { RBRACE }
  | '['             { LBRACKET }
  | ']'             { RBRACKET }
  | ':'             { COLON }
  | ';'             { SEMI }
  | '.'             { DOT }
  | '='             { EQ }
  | '<'             { LT }
  | '>'             { GT }
  | '|'             { BAR }
  | '&'             { AMP }
  | '+'             { PLUS }
  | '-'             { MINUS }
  | '*'             { STAR }
  | '/'             { SLASH }
  | '^'             { CARET }
  | '?'             { QUERY }
  | eof             { EOF }
  | _ as c          { error lexbuf (Printf.sprintf "unexpected character '%c'" c) }

(* Nested block comments; `depth` counts the already-open inner comments. *)
and comment depth = parse
  | "*)"  { if depth = 0 then token lexbuf else comment (depth - 1) lexbuf }
  | "(*"  { comment (depth + 1) lexbuf }
  | '\n'  { Lexing.new_line lexbuf; comment depth lexbuf }
  | eof   { error lexbuf "unterminated comment" }
  | _     { comment depth lexbuf }

and string_lit = parse
  | '"'        { Buffer.contents string_buf }
  | "\\n"      { Buffer.add_char string_buf '\n'; string_lit lexbuf }
  | "\\t"      { Buffer.add_char string_buf '\t'; string_lit lexbuf }
  | "\\\""     { Buffer.add_char string_buf '"';  string_lit lexbuf }
  | "\\\\"     { Buffer.add_char string_buf '\\'; string_lit lexbuf }
  | '\n'       { error lexbuf "unterminated string literal" }
  | eof        { error lexbuf "unterminated string literal" }
  | _ as c     { Buffer.add_char string_buf c; string_lit lexbuf }
