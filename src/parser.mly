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
%token STAR
%token <string> OPERATOR
%token DOT
// connectives
%token SEMI COMMA
// structure
%token RPAREN LPAREN LBRACE RBRACE EOF

%token COLON

%token UNDERSCORE

%type <SurfaceAst.op> op
%type <SurfaceAst.op list> arg_list

%type <SurfaceAst.lhs SurfaceAst.r_init> ref_op

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
  | LET; lbl = expr_label; p = patt; EQ; ~ = lhs; IN; body = expr; <Let>
  | IF; lbl = expr_label; x = cond_expr; THEN; thenc = expr; ELSE; elsec = expr; <Cond>
  | x = ID; ASSIGN; y = lhs; <Assign>
(*  | b = ID; DOT; f = ID; ASSIGN; y = lhs; <FAssign>*)
  | call = fn_call; <Call>
  | ALIAS; lbl = expr_label; LPAREN; x = ID; EQ; y = ap; RPAREN; <Alias>
  | ASSERT; LPAREN; op1 = op; cond = rel_op; op2 = op; RPAREN; { Assert { op1; cond; op2 } }
  | ~ = ID; <Var>
  | ~ = INT; <Int>

let ap :=
  | ~ = ID; <Ast.AVar>
  | STAR; ~ = ap; <Ast.ADeref>
  | v = ID; DOT; ind = INT; { Ast.AProj (Ast.AVar v, ind) }
  | LPAREN; ~ = ap; RPAREN; DOT; ~ = INT; <Ast.AProj>

let patt :=
  | RPAREN; plist = separated_list(COMMA, patt); LPAREN; <Ast.PTuple>
  | UNDERSCORE; { Ast.PNone }
  | ~ = ID; <Ast.PVar>

let op :=
  | ~ = INT; <`OInt>
  | ~ = ID; <`OVar>
  | STAR; ~ = ID; <`ODeref>
  | UNDERSCORE; { `Nondet }

let ref_op :=
  | o = lhs; { (o :> lhs r_init) }
(*  | RBRACE; ~ = separated_list(SEMI, separated_pair(ID, COLON, ref_op)); LBRACE; <`Record>*)

let cond_expr :=
  | ~ = ID; <`Var>
  | b = bin_op; { (b :> [ `BinOp of (op * string * op) | `Var of string]) }

let bin_op := o1 = op; op_name = OPERATOR; o2 = op; <`BinOp>

let lhs :=
  | b = bin_op; { (b :> lhs) }
  | o = op; { (o :> lhs) }
  | MKREF; ~ = ref_op; <`Mkref>
  | ~ = fn_call; <`Call>
(*  | b = op; DOT; ~ = ID; <`Field>*)
  | LPAREN; l = separated_list(COMMA, lhs); RPAREN; <`Tuple>

let fn_call := ~ = callee; lbl = expr_label; arg_names = arg_list; <>
let callee :=
  | ~ = ID; <>
  | LPAREN; ~ = OPERATOR; RPAREN; <>

let rel_op :=
  | ~ = OPERATOR; <>
  | EQ; { "=" }

let expr_label := COLON; ~ = INT; <> | { LabelManager.register () }
