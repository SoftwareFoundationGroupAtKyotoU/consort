open Ast
open Format
open PrettyPrint

let is_operator_id s =
  let lbux = Lexing.from_string s in
  let t = Lexer.read lbux in
  match t with
  | Parser.ID _ -> false
  | _ -> true

let pprint_fn_call { callee; arg_names; label } ff =
  let pp_callee = if is_operator_id callee then
      "(" ^ callee ^ ")"
    else callee
  in
  fprintf ff "%s:%d(%s)" pp_callee label @@ String.concat ", " arg_names

let pp_rinit = function
  | RNone -> ps "_"
  | RVar v -> pv v
  | RInt i -> pprint_int i

let pp_imm = function
  | IInt i -> pprint_int i
  | IVar v -> pv v

let pprint_kv (k,v) =
  pl [
    pf "%s: " k;
    pp_rinit v
  ]

let upp_imm = ul pp_imm
    
let pp_ap r =
  let open Paths in
  (* private tuple types are very annoying *)
  let (root,steps,suff) = (r : concr_ap :> root * steps list * suff) in
  match root,suff with
  | Var var,`None ->
    let rec loop s =
      match s with
      | [] -> ps var
      | `Proj i::`Deref::l ->
        pf "(*%a).%d" (ul loop) l i
      | `Proj i::l ->
        pf "%a.%d" (ul loop) l i
      | `Deref::l -> pf "*%a" (ul loop) l
    in
    loop steps
  | _ -> failwith "Unsupported operation ap"

let rec pp_ref_ast (r: RefinementTypes.concr_refinement) =
  let open RefinementTypes in
  match r with
  | Top -> ps "T"
  | ConstEq n -> pf "~ = %d" n
  | Relation { rel_op1; rel_cond; rel_op2 } ->
    let print_rimm ff = function
      | RConst i -> pi i ff
      | RAp c -> ps (Paths.to_z3_ident c) ff
    in
    let r1_printer ff r1 = match r1 with
      | Nu -> ps "~" ff
      | RImm i -> print_rimm ff i
    in
    pf "%a@ %s@ %a"
      r1_printer rel_op1
      rel_cond
      print_rimm rel_op2
  | And (r1,r2) ->
    pf "%a@ /\\@ %a"
      (ul pp_ref_ast) r1
      (ul pp_ref_ast) r2
  | _ -> failwith @@ "Cannot annotate with relation " ^ (string_of_refinement r)

let pp_lhs = function
  | Var x -> pv x
  | Const i -> pi i
  | Mkref il -> pl [
                    ps "mkref ";
                    pp_rinit il
                  ]
  | Tuple rinit ->
    pl [
        ps "(";
        psep ", " @@ List.map pp_rinit rinit;
        ps ")"
      ]
  | Deref v -> pl [
                   ps "*";
                   pv v
                 ]
  | Call c -> pprint_fn_call c
  | Nondet None -> ps "_"
  | Nondet (Some nref) ->
    pb [
        pf "(_@ :@ %a)" (ul pp_ref_ast) nref
      ]
  | Null -> ps "null"
  | MkArray v -> pl [ ps "mkarray "; pv v ]
  | Read (b,i) ->
    pf "%s[%s]" b i
  | LengthOf v ->
    pf "%s.length" v

let rec pp_patt = function
  | PVar v -> pv v
  | PNone -> ps "_"
  | PTuple l -> pl [
                    ps "(";
                    psep ", " @@ List.map pp_patt l;
                    ps ")"
                  ]   

let rec pp_expr ~ip:((po_id,pr_id) as ip) ~annot (id,e) =
  let e_printer =
    match e with
    | Seq (e1, e2) ->
      pl [
          maybe_brace ~ip ~annot e1;
          semi;
          pp_expr ~ip ~annot e2
        ]
    | Let (patt, lhs, body) ->
      maybe_brace ~ip ~annot ~all_seq:true ~pre:(pl [
            pf "let%a %a = %a in "
              po_id id
              (ul pp_patt) patt
              (ul pp_lhs) lhs
          ]) body
    | Assign (x, y, e) ->
      pl [
          pf "%a%s := %a" pr_id id x (ul pp_imm) y;
          semi;
          pp_expr ~ip ~annot e
        ]
    | Update (x,ind,y,e') ->
      pl [
          pf "%a%s[%s] <- %s" pr_id id x ind y;
          semi;
          pp_expr ~ip ~annot e'
        ]
    | NCond (v,tr,fl) ->
      pp_cond ~ip ~annot id "ifnull" v tr fl
    | Cond (x,tr,fl) ->
      pp_cond ~ip ~annot id "if" x tr fl
    | Alias(x,y,e) ->
      pl [
          pf "alias%a(%a = %a)" po_id id (ul pp_ap) x (ul pp_ap) y;
          semi;
          pp_expr ~ip ~annot e
        ]
    | Assert ({ rop1; cond; rop2 },e) ->
      pl [
          pf "assert%a(%a %s %a)" po_id id upp_imm rop1 cond upp_imm rop2;
          semi;
          pp_expr ~ip ~annot e
        ]
    | Unit -> ps "()"
    | Return v -> pf "return%a %s" po_id id v
    | Fail -> ps "fail"
    | Match (e1, e2, h, r, e3) ->
      pl [
        pf "match %a with" (ul pp_lhs) e1;
        pf "| Nil -> {";
        pp_expr ~ip ~annot e2;
        ps "}";
        pf "| Cons(%s,%s) -> {" h r;
        pp_expr ~ip ~annot e3;
        ps "}";
      ]
  in
  match e with
  | Seq _ -> e_printer
  | _ -> (fun ff ->
      annot id e ff;
      e_printer ff)
and pp_cond ~ip:((po_id,_) as ip) ~annot id cond v tr fl =
  pblock
    ~nl:false
    ~op:(pf "%s%a %s then {" cond po_id id v)
    ~body:(pp_expr ~ip ~annot tr)
    ~close:(
      pblock ~nl:true ~op:(ps "} else {")
        ~body:(pp_expr ~ip ~annot fl)
        ~close:(ps "}")
    )


and maybe_brace ~ip ~annot ?(all_seq=false) ?pre ((_,e) as tagged_e) : formatter -> unit =
  let need_block = 
      match e with
      | Seq _ -> true
      | Alias _ when all_seq -> true
      | Assert _ when all_seq -> true
      | Assign _ when all_seq -> true
      | Update _ when all_seq -> true
      | _ -> false
  in
  if need_block then
    pl [
      indent_from_here;
      (match pre with Some f -> f | None -> null);
      ps "{"; newline;
      pp_expr ~ip ~annot tagged_e; dedent; newline;
      ps "}"
    ]
  else
    pl [
      (match pre with
        Some f -> pl [ f; newline ]
      | None -> null);
      pp_expr ~ip ~annot tagged_e
    ]

let pprint_fn ~ip ~annot_fn ~annot ff {name; args; body} =
  pl [
    annot_fn name;
    pblock
      ~nl:true
      ~op:(pf "%s(%s) {" name @@ String.concat ", " args)
      ~body:(pp_expr ~ip ~annot body)
      ~close:(ps "}");
  ] ff

let pprint_prog ~ip ~annot_fn ~annot ff (fn,body) =
  pp_open_vbox ff 0;
  List.iter (pprint_fn ~ip ~annot_fn ~annot ff) fn;
  pp_close_box ff ();
  pp_open_vbox ff 1;
  fprintf ff "{@;";
  pp_expr ~ip ~annot body ff;
  pp_close_box ff ();
  pp_force_newline ff (); pp_print_string ff "}"

let id_printer labels =
  if labels then
    (fun ff (id,_) -> pf ":%d" id ff),(fun ff (id,_) -> pf "%d:" id ff)
  else
    (fun _ _ -> ()),(fun _ _ -> ())
    
let pretty_print_program ?(with_labels=true) ?(annot_fn=(fun _ _ -> ())) ?(annot=(fun _ _ _ -> ())) out_chan prog =
  let ff = Format.formatter_of_out_channel out_chan in
  pprint_prog ~ip:(id_printer with_labels) ~annot_fn ~annot ff prog;
  Format.pp_print_newline ff ()
