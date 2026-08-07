{
open Parser

exception Error of string * Lexing.position
}

let digit = ['0'-'9']
let white = [' ' '\t']+

rule token = parse
  | white          { token lexbuf }
  | '\n'           { Lexing.new_line lexbuf; token lexbuf }
  | digit+ as n    { INT (int_of_string n) }
  | '+'            { PLUS }
  | '-'            { MINUS }
  | '*'            { TIMES }
  | '/'            { DIV }
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | eof            { EOF }
  | _ as c
      { raise (Error (Printf.sprintf "unexpected character '%c'" c,
                      Lexing.lexeme_start_p lexbuf)) }
