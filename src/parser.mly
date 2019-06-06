%{
	open SurfaceAst

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

%token COLON

%token UNDERSCORE

// relations
%token LT LEQ NEQ GE GT

%type <SurfaceAst.op> op
%type <SurfaceAst.op list> arg_list 

%start <SurfaceAst.prog> prog

%%

let prog := ~ = fdef* ; ~ = delimited(LBRACE, expr, RBRACE); EOF; <>

let fdef := name = ID ; args = param_list; body = expr; <>

let param_list :=
  | ~ = delimited(LPAREN, separated_nonempty_list(COMMA, ID), RPAREN); <>
  | UNIT; { [] }

let arg_list :=
  | ~ = delimited(LPAREN, separated_nonempty_list(COMMA, op), RPAREN); <>
  | UNIT; { [] }

let expr :=
  | UNIT; { Unit }
  | ~ = delimited(LBRACE, expr, RBRACE); <>
  | LBRACE; e = expr; SEMI; rest = separated_nonempty_list(SEMI, expr); RBRACE; {
		list_to_seq e rest
	  }
  | LET; lbl = expr_label; x = ID; EQ; ~ = lhs; IN; body = expr; <Let>
  | IF; lbl = expr_label; x = ID; THEN; thenc = expr; ELSE; elsec = expr; <Cond>
  | x = ID; ASSIGN; y = lhs; <Assign>
  | call = fn_call; <Call>
  | ALIAS; lbl = expr_label; LPAREN; x = ID; EQ; y = ID; RPAREN; <Alias>
  | ASSERT; LPAREN; op1 = op; cond = relation; op2 = op; RPAREN; { Assert { op1; cond; op2 } }
  | ~ = ID; <Var>
  | ~ = INT; <Int>

let op :=
  | ~ = INT; <`OInt>
  | ~ = ID; <`OVar>
  | STAR; ~ = ID; <`ODeref>
  | UNDERSCORE; { `Nondet }

let lhs :=
  | o = op; { (o :> lhs) }
  | MKREF; ~ = op; <`Mkref>
  | o1 = op; PLUS; o2 = op; <`Plus>
  | ~ = fn_call; <`Call>

let relation :=
  | LT; { `Lt }
  | LEQ; { `Leq }
  | NEQ; { `Neq }
  | EQ; { `Eq }
  | GT; { `Gt }
  | GE; { `Ge }

let fn_call := callee = ID; lbl = expr_label; arg_names = arg_list; <>

let expr_label := COLON; ~ = INT; <> | { LabelManager.register () }
