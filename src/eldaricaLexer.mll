{
open EldaricaParser

let next_line = Lexing.new_line
}

let nat = ['0'-'9']+

let white = [' ' '\t']+
let newline = '\n'
let id_rest = ['a'-'z' 'A'-'Z' '0'-'9' '_' '*' '$' '>']
let id = ('_' id_rest+ | ['a' - 'z' 'A'-'Z'] id_rest*)
let program_start = "program_start"

rule read =
  parse
  | white    { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | nat { let i = int_of_string @@ Lexing.lexeme lexbuf in NAT i }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | "()" { UNIT }
  | "->" { ARROW }
  | "-" { BAR }
  | ":" { COLON }
  | "," { COMMA }
  | "true" {NAT(1) }
  | "false" { NAT(0) }
  | program_start { START}
  | "FALSE" {FALSE}
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { failwith @@ "Invalid token " ^ (Lexing.lexeme lexbuf) }
