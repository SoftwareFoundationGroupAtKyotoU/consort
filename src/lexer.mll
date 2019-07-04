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
let id_rest = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let id = ('_' id_rest+ | ['a' - 'z' 'A'-'Z'] id_rest*)
let non_comment = [^ '/' '*' ]+
let comment_delim = [ '/' '*' ]
let operators = ['+' '-' '*' '/' '%' '<' '>' '=' '!']+

rule read =
  parse
  | "/*" { comment lexbuf; read lexbuf }
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
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '.' { DOT }
  | '=' { EQ }
  | ":=" { ASSIGN }
  | operators { OPERATOR (Lexing.lexeme lexbuf) }
  | '_' { UNDERSCORE }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
and comment =
  parse
  | non_comment { comment lexbuf }
  | "*/" { () }
  | "/*" { comment lexbuf; comment lexbuf }
  | comment_delim { comment lexbuf }
