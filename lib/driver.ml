(* Parsing entry point built on menhir's incremental API, so errors carry the
   exact position and offending token instead of a bare Parser.Error. *)

module I = Parser.MenhirInterpreter

type error = {
  message : string;
  line : int;  (* 1-based *)
  col : int;   (* 0-based *)
}

let line_col (pos : Lexing.position) = (pos.pos_lnum, pos.pos_cnum - pos.pos_bol)

let parse (src : string) : (Ast.expr, error) result =
  let lexbuf = Lexing.from_string src in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.token lexbuf in
  let checkpoint = Parser.Incremental.program lexbuf.lex_curr_p in
  try
    I.loop_handle
      (fun ast -> Ok ast)
      (fun _checkpoint ->
        let line, col = line_col (Lexing.lexeme_start_p lexbuf) in
        let token = Lexing.lexeme lexbuf in
        let message =
          if token = "" then "syntax error: unexpected end of input"
          else Printf.sprintf "syntax error: unexpected token '%s'" token
        in
        Error { message; line; col })
      supplier checkpoint
  with Lexer.Error (msg, pos) ->
    let line, col = line_col pos in
    Error { message = msg; line; col }

(* Render an error with the offending source line and a caret under it. *)
let render ~src { message; line; col } =
  let src_line =
    match List.nth_opt (String.split_on_char '\n' src) (line - 1) with
    | Some l -> l
    | None -> ""
  in
  Printf.sprintf "%d:%d: %s\n  %s\n  %s^" line col message src_line
    (String.make col ' ')
