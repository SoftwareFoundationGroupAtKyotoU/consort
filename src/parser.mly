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

// types
%token DOLLAR INT_T REF TOP
%token GAMMA
%token ARROW
%token NU AND
%token <float> FLOAT

%left AND

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

let seq :=
  | ~ = expr; RBRACE; { [expr] }
  | RBRACE; { [] }
  | ~ = expr; SEMI; ~ = seq; { expr::seq }


let expr :=
  | UNIT; { Unit }
  | ~ = delimited(LBRACE, expr, RBRACE); <>
  | LBRACE; e = expr; SEMI; rest = seq; {
		list_to_seq e rest
	  }
  | LET; lbl = expr_label; p = patt; EQ; ~ = lhs; IN; body = expr; <Let>
  | IF; lbl = expr_label; x = cond_expr; THEN; thenc = expr; ELSE; elsec = expr; <Cond>
  | lbl = pre_label; x = ID; ASSIGN; y = lhs; <Assign>
  | call = fn_call; <Call>
  | ALIAS; lbl = expr_label; LPAREN; x = ID; EQ; y = ap; RPAREN; <Alias>
  | ASSERT; lbl = expr_label; LPAREN; op1 = op; cond = rel_op; op2 = op; RPAREN; { Assert (lbl,{ op1; cond; op2 }) }
  | GAMMA; lbl = expr_label; LBRACE; ~ = ty_env; RBRACE; <EAnnot>
  | ~ = var_ref; <>
  | ~ = INT; <Int>

let ty_env == separated_list(SEMI, separated_pair(ID, COLON, typ))

let var_ref :=
  | ~ = ID; ~ = expr_label; <Var>

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
  | STAR; ~ = ID; <`ODeref>
  | UNDERSCORE; { `Nondet }
  | LPAREN; o = bin_op; RPAREN; { (o :> op) }

let tuple_rest :=
  | l = lhs; COMMA; { [l] }
  | l = lhs; { [l] }
  | l1 = lhs; COMMA; l2 = tuple_rest; { l1::l2 }

let tuple_contents :=
  | l = lhs; COMMA; { [l] }
  | l1 = lhs; COMMA; l2 = tuple_rest; { l1::l2 }

let ref_op :=
  | o = lhs; { (o :> lhs) }

let cond_expr :=
  | ~ = ID; <`Var>
  | b = bin_op; { (b :> [ `BinOp of (op * string * op) | `Var of string | `Nondet]) }
  | UNDERSCORE; { `Nondet }

let bin_op :=
  | o1 = op; op_name = operator; o2 = op; <`BinOp>

let operator :=
  | ~ = OPERATOR; <>
  | EQ; { "=" }
  | STAR; { "*" }

let lhs :=
  | b = bin_op; { (b :> lhs) }
  | o = op; { (o :> lhs) }
  | MKREF; ~ = ref_op; <`Mkref>
  | ~ = fn_call; <`Call>
  | LPAREN; l = tuple_contents; RPAREN; <`Tuple>

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
  | ~ = typ; REF; o = FLOAT; { RefinementTypes.Ref (typ, RefinementTypes.OConst o) }
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
