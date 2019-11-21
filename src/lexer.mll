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
let nonquote = [^'"']+

rule read =
  parse
  | "##pos" { let (nm,pos) = pd1 lexbuf in
              Locations.set_file_name lexbuf nm pos;
              read lexbuf }
  | "//" { line_comment lexbuf; read lexbuf }
  | "/*" { comment lexbuf; read lexbuf }
  | "/**" { comment lexbuf; read lexbuf }
  | white    { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | "()" { UNIT }
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
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | "/\\" { AND }
  | '.' { DOT }
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
  | "/**" { comment lexbuf; comment lexbuf }
  | comment_delim { comment lexbuf }
and line_comment =
  parse
  | not_newline { line_comment lexbuf }
  | newline { next_line lexbuf }
and pd1 =
  parse
  | white { pd1 lexbuf }
  | '"' { str_content lexbuf }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
and str_content =
  parse
  | nonquote { end_str (Lexing.lexeme lexbuf) lexbuf }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
and end_str nm =
  parse
  | '"' { pd2 nm lexbuf }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
and pd2 nm =
  parse
  | white { pd2 nm lexbuf }
  | int { let v = int_of_string @@ Lexing.lexeme lexbuf in pd3 (nm,v) lexbuf }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
and pd3 g =
  parse
  | white { pd3 g lexbuf }
  | newline { next_line lexbuf; g }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
