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
  | Nondet -> ps "_"

let rec pp_patt = function
  | PVar v -> pv v
  | PNone -> ps "_"
  | PTuple l -> pl [
                    ps "(";
                    psep ", " @@ List.map pp_patt l;
                    ps ")"
                  ]

let pp_ap = function
  | AVar v -> pv v
  | ADeref v -> pl [ ps "*"; pv v ]
  | AProj (v,ind) -> pl [ pv v; ps "."; pi ind ]
  | APtrProj (v,ind) -> pl [ pf "(*%s)." v; pi ind ]

let upp_imm = ul pp_imm

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
    | Cond (x,tr,fl) ->
      pl [
          indent_from_here;
          pf "if%a %s then {" po_id id x; newline;
          pp_expr ~ip ~annot tr; dedent; newline;
          indent_from_here; ps "} else {"; newline;
          pp_expr ~ip ~annot fl; dedent; newline; ps "}"
        ]
    | Alias(x,y,e) ->
      pl [
          pf "alias%a(%s = %a)" po_id id x (ul pp_ap) y;
          semi;
          pp_expr ~ip ~annot e
        ]
    | Assert ({ rop1; cond; rop2 },e) ->
      pl [
          pf "assert%a(%a %s %a)" po_id id upp_imm rop1 cond upp_imm rop2;
          semi;
          pp_expr ~ip ~annot e
        ]
    | EVar v -> pl [
                    pv v;
                    po_id () id
                  ]
  in
  match e with
  | Seq _ -> e_printer
  | _ -> (fun ff ->
      annot id ff;
      e_printer ff)

and maybe_brace ~ip ~annot ?(all_seq=false) ?pre ((_,e) as tagged_e) : formatter -> unit =
  let need_block = 
      match e with
      | Seq _ -> true
      | Alias _ when all_seq -> true
      | Assert _ when all_seq -> true
      | Assign _ when all_seq -> true
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

let pprint_fn ~ip ~annot ff {name; args; body} =
  let open Format in begin
    pl [
      indent_from_here;
      pf "%s(%s)" name @@ String.concat ", " args;
      ps "{"; newline;
      pp_expr ~ip ~annot body;
      dedent; newline; ps "}"
    ] ff;
    pp_force_newline ff ()
  end

let pprint_prog ~ip ~annot ff (fn,body) =
  List.iter (pprint_fn ~ip ~annot ff) fn;
  pp_open_vbox ff 1;
  fprintf ff "{@;";
  pp_expr ~ip ~annot body ff;
  pp_close_box ff ();
  pp_force_newline ff (); pp_print_string ff "}"

let id_printer labels =
  if labels then
    (fun () id -> pf ":%d" id),(fun () id -> pf "%d:" id)
  else
    (fun () _ -> (fun _ff -> ())),(fun () _ -> (fun _ff -> ()))
    

let pretty_print_program ?(with_labels=true) ?(annot=(fun _ _ -> ())) = pretty_print_gen (pprint_prog ~ip:(id_printer with_labels) ~annot)
let pretty_print_expr ?(with_labels=true) ?(annot=(fun _ _ -> ())) = pretty_print_gen (fun ff e -> pp_expr ~ip:(id_printer with_labels) ~annot e ff)
let pretty_print_fn ?(with_labels=true) ?(annot=(fun _ _ -> ())) = pretty_print_gen (pprint_fn ~ip:(id_printer with_labels) ~annot)
