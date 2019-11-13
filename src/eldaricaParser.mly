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

%type <CounterExampleDAG.graph> graph

%start graph

%%
let graph := ID;~=node*;EOF;<>
let node := 
  | id = NAT; COLON; FALSE; ARROW; dst = int_list; {{id; ty=False; args=[]; dst}}
  | id = NAT; COLON; START; args = param_list; {{id; ty=Goal; args; dst=[]}}
  | id = NAT; COLON; ty = node_type; args = param_list; ARROW; dst = int_list; {{id; ty; args; dst}} 

let node_type := 
  | name = ID ;BAR; line=NAT; BAR; t = ID ;{
      begin
    match t with 
    | "var" -> Var(name, line)
    | "let" -> Let(name, line)
    | "seq" -> Seq(name, line)
    | "ifz" -> If(name, line)
    | "assert" -> Assert (name, line)
    | "alias" -> Alias (name, line)
    | "update" -> Update (name, line)
    | "assign" -> Assign(name, line)
    | _ -> failwith "Tuple, Array, Null is not implemented"
      end

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
let integer := 
    | BAR ;i = NAT ; {-i}
    | ~=NAT ; <>
