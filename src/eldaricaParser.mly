%{
  open CounterExampleDAG
%}
%token <int> NAT
%token <string> ID
%token UNIT
%token COMMA
%token RPAREN LPAREN EOF
%token COLON 
%token BAR
%token ARROW
%token FALSE START
%token True False

%type <CounterExampleDAG.graph> graph

%start graph

%%
let graph := ID;~=node*;EOF;<>
let node := 
  | id = NAT; COLON; FALSE; ARROW; dst = dst; {{id; ty=False; args=[]; dst}}
  | id = NAT; COLON; START; args = param_list; {{id; ty=Goal; args; dst=[]}}
  | id = NAT; COLON; ty = node_type; args = param_list; ARROW; dst = dst; {{id; ty; args; dst}} 
  | id = NAT; COLON; ty = node_type; args = param_list; {{id; ty; args; dst=[]}}

let node_type := 
  | name = ID ;BAR; line=NAT; BAR; t = ID ;{
    Ast(
      begin
    match t with 
    | "var" -> Var
    | "let" -> Let
    | "seq" -> Seq
    | "ifz" -> If
    | "ifnull" -> IfNull
    | "assert" -> Assert 
    | "alias" -> Alias 
    | "update" -> Update 
    | "assign" -> Assign
    | _ -> failwith "Tuple, Array, Null is not implemented"
      end
      , name, line)

  }
  | name = ID ;BAR; inout=ID ;{
    match inout  with
    | "in" -> CallIn(name)
    | "out" -> CallOut(name)
    | _ -> failwith "invalid inout"
  }

let param_list :=
  | ~ = delimited(LPAREN, int_list, RPAREN); <>
  | UNIT; { [] }

let int_list :=
  | ~ = separated_nonempty_list(COMMA, integer); <>

let dst := int_list
let integer := 
    | BAR ;i = NAT ; {-i}
    | ~=NAT ; <>



