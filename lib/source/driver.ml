(* Parsing entry point built on menhir's incremental API, so errors carry the
   exact position and offending token instead of a bare Parser.Error. *)

module I = Parser.MenhirInterpreter

type error = {
  message : string;
  line : int;  (* 1-based *)
  col : int;   (* 0-based *)
}

let line_col (pos : Lexing.position) = (pos.pos_lnum, pos.pos_cnum - pos.pos_bol)

(* Every later stage reports positions the same way, so they can all be
   rendered by `render` below. *)
let error_at (loc : Ast.loc) (message : string) : error =
  let line, col = line_col loc.start_p in
  { message; line; col }

let parse_with entry (src : string) =
  let lexbuf = Lexing.from_string src in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.token lexbuf in
  let checkpoint = entry lexbuf.lex_curr_p in
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

let parse (src : string) : (Ast.program, error) result =
  parse_with Parser.Incremental.program src

(* Parse the contents of a .scei interface file. *)
let parse_intf (src : string) : (Ast.intf, error) result =
  parse_with Parser.Incremental.intf_file src

(* Render an error with the offending source line and a caret under it. A node
   synthesized by the front end carries Ast.dummy_loc, whose line/col are out of
   range; print the message alone rather than a location that is not in the file. *)
let render ~src { message; line; col } =
  if line < 1 || col < 0 then message
  else
    let src_line =
      match List.nth_opt (String.split_on_char '\n' src) (line - 1) with
      | Some l -> l
      | None -> ""
    in
    Printf.sprintf "%d:%d: %s\n  %s\n  %s^" line col message src_line
      (String.make col ' ')