{
open Parser

let next_line lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1 }
}

let int = '-'? ['0'-'9']+

let white = [' ' '\t']+
let newline = '\n'
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

(* part "4" *)
rule read =
  parse
  | white    { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | "()" { UNIT }
  | int { INT (int_of_string @@ Lexing.lexeme lexbuf) }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "let" { LET }
  | "in" { IN }
  | '*' { STAR }
  | ';' { SEMI }
  | ':' { COLON }
  | ',' { COMMA }
  | "mkref" { MKREF }
  | "alias" { ALIAS }
  | "assert" { ASSERT }
  | '+' { PLUS }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '=' { EQ }
  | ":=" { ASSIGN }
  | '<' { LT }
  | "<=" { LEQ }
  | "!=" { NEQ }
  | '_' { UNDERSCORE }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
