%{
	open Ast

	let list_to_seq x rest =
	  let comp = x::rest in
	  let rev = List.rev comp in
	  let accum = List.hd rev in
	  List.fold_left (fun curr next  ->
					   Seq (next, curr)) accum (List.tl rev)
%}
// values
%token UNIT
%token <int> INT
%token <string> ID
// conditionals
%token IF THEN ELSE
// bindings
%token LET IN MKREF EQ
// BIFs
%token ASSERT ALIAS
// Update
%token ASSIGN
// operators
%token PLUS STAR
// connectives
%token SEMI COMMA
// structure
%token RPAREN LPAREN LBRACE RBRACE EOF

%token UNDERSCORE

// relations
%token LT LEQ NEQ

%start <Ast.prog> prog

%%

let prog := ~ = fdef* ; ~ = delimited(LBRACE, expr, RBRACE); EOF; <>

let fdef := name = ID ; args = arg_list; body = expr; {
		{name; args; body}
	  }

let arg_list :=
  | ~ = delimited(LPAREN, separated_nonempty_list(COMMA, ID), RPAREN); <>
  | UNIT; { [] }

let expr :=
  | UNIT; { Unit }
  | ~ = delimited(LBRACE, expr, RBRACE); <>
  | LBRACE; e = expr; SEMI; rest = separated_nonempty_list(SEMI, expr); RBRACE; {
		list_to_seq e rest
	  }
  | LET; x = ID; EQ; ~ = lhs; IN; body = expr; <Let>
  | IF; x = ID; THEN; thenc = expr; ELSE; elsec = expr; <Cond>
  | x = ID; ASSIGN; y = ID; <Assign>
  | call = fn_call; <ECall>
  | ALIAS; LPAREN; x = ID; EQ; y = ID; RPAREN; <Alias>
  | ASSERT; LPAREN; x = ID; cond = relation; y = ID; RPAREN; { Assert(cond, x, y) }
  | ~ = ID; <EVar>
  | ~ = INT; <EInt>

let relation :=
  | LT; { Lt }
  | LEQ; { Leq }
  | NEQ; { Neq }
  | EQ; { Eq }

let lhs :=
  | ~ = ID; <Var>
  | c = fn_call; <Call>
  | ~ = INT; <Const>
  | MKREF; ~ = ref_cont; <Mkref>
  | STAR; ~ = ID; <Deref>
  | STAR; { Nondet }
  | v1 = ID; PLUS; v2 = ID; <Plus>

let fn_call := callee = ID; arg_names = arg_list; { {callee; arg_names} }

let ref_cont :=
  | ~ = ID; <RVar>
  | ~ = INT; <RInt>
  | UNDERSCORE; { RNone } 
