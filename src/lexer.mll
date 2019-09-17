{
open Parser

let next_line = Lexing.new_line
}

let int = '-'? ['0'-'9']+

let float = '-'?['0'-'9']+ '.' ['0' - '9']*

let white = [' ' '\t']+
let newline = '\n'
let id_rest = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let id = ('_' id_rest+ | ['a' - 'z' 'A'-'Z'] id_rest*)
let non_comment = [^ '/' '*' '\n']+
let comment_delim = [ '/' '*' ]
let operators = ['+' '-' '*' '/' '%' '<' '>' '=' '!' '&' '^' '|' '#' '@']+
let not_newline = [^'\n']+

rule read =
  parse
  | "//" { line_comment lexbuf; read lexbuf }
  | "/*" { comment lexbuf; read lexbuf }
  | white    { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | "()" { UNIT }
  | float { FLOAT (float_of_string @@ Lexing.lexeme lexbuf) }
  | int { let i = int_of_string @@ Lexing.lexeme lexbuf in LabelManager._internal_incr i; INT i }
  | "ifnull" { IFNULL }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "let" { LET }
  | "in" { IN }
  | "length" { LENGTH }
  | '*' { STAR }
  | ';' { SEMI }
  | ':' { COLON }
  | ',' { COMMA }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | "<-" { LARROW }
  | "mkref" { MKREF }
  | "mkarray" { MKARRAY }
  | "alias" { ALIAS }
  | "assert" { ASSERT }
  | "true" { TRUE }
  | "false" { FALSE }
  | "$gamma" { GAMMA }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | "/\\" { AND }
  | '.' { DOT }
  | "int" { INT_T }
  | "ref" { REF }
  | '=' { EQ }
  | 'T' { TOP }
  | "->" { ARROW }
  | '~' { NU }
  | '$' { DOLLAR }
  | ":=" { ASSIGN }
  | "null" { NULL }
  | operators { OPERATOR (Lexing.lexeme lexbuf) }
  | '_' { UNDERSCORE }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
and comment =
  parse
  | newline { next_line lexbuf; comment lexbuf }
  | non_comment { comment lexbuf }
  | "*/" { () }
  | "/*" { comment lexbuf; comment lexbuf }
  | comment_delim { comment lexbuf }
and line_comment =
  parse
  | not_newline { line_comment lexbuf }
  | newline { next_line lexbuf; () }
