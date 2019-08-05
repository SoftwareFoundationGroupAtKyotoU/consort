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
%token NULL
%token TRUE FALSE
// conditionals
%token IF THEN ELSE IFNULL
// bindings
%token LET IN MKREF EQ
// arrays
%token MKARRAY LBRACKET RBRACKET LARROW
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

// types
%token DOLLAR INT_T REF TOP
%token GAMMA
%token ARROW
%token NU AND
%token <float> FLOAT

%left AND

%type <SurfaceAst.lhs> lhs

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

let seq :=
  | ~ = expr; RBRACE; { [expr] }
  | RBRACE; { [] }
  | ~ = expr; SEMI; ~ = seq; { expr::seq }

let array_expr :=
  | base = op; LBRACKET; ind = op; RBRACKET; <>

let expr :=
  | UNIT; ~ = expr_label; <Unit>
  | ~ = delimited(LBRACE, expr, RBRACE); <>
  | LBRACE; e = expr; SEMI; rest = seq; {
		list_to_seq e rest
	  }
  | LET; lbl = expr_label; p = patt; EQ; ~ = lhs; IN; body = expr; <Let>
  | IF; lbl = expr_label; x = cond_expr; THEN; thenc = expr; ELSE; elsec = expr; <Cond>
  | IFNULL; lbl = expr_label; ~ = ID; THEN; thenc = expr; ELSE; elsec = expr; <NCond>
  | lbl = pre_label; x = ID; ASSIGN; y = lhs; <Assign>
  | ALIAS; lbl = expr_label; LPAREN; x = ID; EQ; y = ap; RPAREN; <Alias>
  | ASSERT; lbl = expr_label; LPAREN; op1 = op; cond = rel_op; op2 = op; RPAREN; { Assert (lbl,{ op1; cond; op2 }) }
  | lbl = pre_label; (b,i) = array_expr; LARROW; y = lhs; {
		Update (lbl,b,i,y)
	  }
  | GAMMA; lbl = expr_label; LBRACE; ~ = ty_env; RBRACE; <EAnnot>
  | lbl = pre_label; ~ = lhs; <Value>

let ty_env == separated_list(SEMI, separated_pair(ID, COLON, typ))

let ap :=
  | ~ = ID; <Ast.AVar>
  | STAR; ~ = ID; <Ast.ADeref>
  | LPAREN; STAR; id = ID; RPAREN; DOT; ind = INT; { Ast.APtrProj(id, ind) }
  | v = ID; DOT; ind = INT; { Ast.AProj (v, ind) }

let patt :=
  | LPAREN; plist = separated_nonempty_list(COMMA, patt); RPAREN; <Ast.PTuple>
  | UNDERSCORE; { Ast.PNone }
  | ~ = ID; <Ast.PVar>

let op :=
  | ~ = INT; <`OInt>
  | ~ = ID; <`OVar>
  | TRUE; { `OBool true }
  | FALSE; { `OBool false }
  | STAR; ~ = ID; <`ODeref>
  | UNDERSCORE; { `Nondet }
  | LPAREN; o = lhs; RPAREN; { o }
  | NULL; { `Null }
  | ~ = fn_call; <`Call>
  | LPAREN; l = tuple_contents; RPAREN; <`Tuple>
  | ~ = array_expr; <`Read>

let tuple_rest :=
  | l = lhs; COMMA; { [l] }
  | l = lhs; { [l] }
  | l1 = lhs; COMMA; l2 = tuple_rest; { l1::l2 }

let tuple_contents :=
  | l = lhs; COMMA; { [l] }
  | l1 = lhs; COMMA; l2 = tuple_rest; { l1::l2 }

let cond_expr :=
  | ~ = ID; <`Var>
  | b = bin_op; { (b :> [ `BinOp of (lhs * string * lhs) | `Var of string | `Nondet]) }
  | UNDERSCORE; { `Nondet }

let bin_op :=
  | o1 = op; op_name = operator; o2 = op; <`BinOp>

let operator :=
  | ~ = OPERATOR; <>
  | EQ; { "=" }
  | STAR; { "*" }

let lhs :=
  | b = bin_op; { (b :> lhs) }
  | o = op; { o }
  | MKREF; ~ = lhs; <`Mkref>
  | MKARRAY; ~ = lhs; <`MkArray>

let fn_call := ~ = callee; lbl = expr_label; arg_names = arg_list; <>
let callee ==
  | ~ = ID; <>
  | LPAREN; ~ = operator; RPAREN; <>

let rel_op :=
  | ~ = OPERATOR; <>
  | EQ; { "=" }

let expr_label == COLON; ~ = INT; <> | { LabelManager.register () }
let pre_label == ~ = INT; COLON; <> | { LabelManager.register () }

let typ :=
  | ~ = refine; INT_T; { RefinementTypes.Int refine }
  | ~ = typ; REF; o = FLOAT; { RefinementTypes.Ref (typ, RefinementTypes.OConst o,`NUnk) }
  | LPAREN; ~ = tup_list; RPAREN; {
		let (m_bind,t_l) =
		  List.mapi (fun i (b_l,t) ->
					  (List.map (fun b -> (b,RefinementTypes.SProj i)) b_l,t)
					) tup_list
		  |> List.split
		in
		RefinementTypes.Tuple (List.concat m_bind,t_l)
	  }

let ap_elem :=
  | STAR; { `Deref }
  | ~ = INT; <`Proj>

let ref_ap :=
  | root = ID; rest = separated_list(ARROW, ap_elem); {
		List.fold_left (fun acc i ->
						 match i with
						 | `Deref -> `ADeref acc
						 | `Proj i -> `AProj (acc,i)
					   ) (`AVar root) rest
	  }

let rel_arg :=
  | DOLLAR; s_var = INT; { RefinementTypes.RAp (`Sym s_var) }
  | ~ = ref_ap; { RefinementTypes.RAp (ref_ap :> RefinementTypes.refine_ap) }
  | i = INT; { RefinementTypes.RConst i }


let refine :=
  | TOP; { RefinementTypes.Top }
  | NU; EQ; n = INT; { RefinementTypes.ConstEq n }
  | NU; op = OPERATOR; arg = rel_arg; {
		let open RefinementTypes in
		Relation { rel_op1 = Nu; rel_cond = op; rel_op2 = arg }
	  }
  | r1 = refine; AND; r2 = refine; <RefinementTypes.And>

let tup_list == separated_nonempty_list(COMMA, tup_typ)
let tup_typ :=
  | DOLLAR; s_var = INT; COLON; ~ = typ; { ([s_var],typ) }
  | ~ = typ; { ([],typ) }
