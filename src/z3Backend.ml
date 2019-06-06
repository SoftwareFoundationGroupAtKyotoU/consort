open Format
open RefinementTypes

let ovar_name ovar = Printf.sprintf "ovar-%d" ovar

let pred_name p = Printf.sprintf "pred-%d" p

let pp_sexpr printer ff =
  pp_open_box ff 2;
  pp_print_string ff "(";
  printer (pp_print_space ff) (fun s -> pp_print_string ff s);
  pp_print_string ff ")";
  pp_close_box ff ()

let rec iter_print ~spc pf l = match l with
  | [] -> ()
  | [h] -> pf h
  | h::t -> pf h; spc (); iter_print ~spc pf t

let rec init i f =
  if i = 0 then []
  else (f i)::(init (i - 1) f)

let print_string_list l ff =
  pp_sexpr (fun spc ps ->
    iter_print ~spc ps l
  ) ff

let psl = print_string_list

let print_generic head l ff =
  pp_sexpr (fun spc ps ->
    ps head; spc ();
    iter_print ~spc (fun susp -> susp ff) l
  ) ff

let pg = print_generic

module IntMap = RefinementTypes.IntMap
module SM = RefinementTypes.SM

let plift s ff = pp_print_string ff s
let pl = plift

let pp_lin_op lo ff = match lo with
  | LConst i -> pp_print_string ff @@ string_of_int i
  | LVar (1,n) -> pp_print_string ff n
  | LVar (0,_) -> pp_print_string ff "0"
  | LVar (k,n) when k > 0 -> print_string_list [ "*"; (string_of_int k) ; n ] ff
  | LVar (k,n) when k < 0 -> print_string_list [ "*"; Printf.sprintf "(- %d)" @@ abs k; n ] ff
  | _ -> assert false

let pp_imm o ff = match o with
  | Ast.IVar v -> pp_print_string ff v
  | Ast.IInt i -> pp_print_string ff @@ string_of_int i

let pp_relop binding r ff = match r with
  | Nu -> pp_print_string ff binding
  | RImm ri -> pp_imm ri ff

let refine_args o l = match o with
  | Some v -> List.filter ((<>) v) l
  | None -> l

let ctxt_var i = "CTXT" ^ (string_of_int i)

let rec pp_refine r binding ff = match r with
  | Pred (i,args,o) ->
    let ctxt = init !KCFA.cfa ctxt_var in
    print_string_list (pred_name i::ctxt @ [ binding ] @ (refine_args o args)) ff
  | CtxtPred (ctxt,i,args,o) ->
    let c_string = (string_of_int ctxt)::(init (!KCFA.cfa-1) (fun i -> ctxt_var @@ i + 1)) in
    print_string_list (pred_name i::c_string @ [ binding ] @ (refine_args o args)) ff
  | Top -> pp_print_string ff "true"
  | ConstEq n -> print_string_list [ "="; binding; string_of_int n ] ff
  | Linear { op1; op2 } ->
    print_generic "=" [
        plift binding;
        print_generic "+" [
          pp_lin_op op1;
          pp_lin_op op2
        ]
      ] ff
  | Relation { rel_op1; rel_cond = Neq; rel_op2 } ->
    pg "not" [ pp_refine (Relation { rel_op1; rel_cond = Eq; rel_op2 }) binding ] ff
  | Relation {rel_op1; rel_cond; rel_op2 } ->
    pg (Ast.cond_to_string rel_cond) [
          pp_relop binding rel_op1;
          pp_imm rel_op2
      ] ff
  | And (r1,r2) ->
    pg "and" [
        pp_refine r1 binding;
        pp_refine r2 binding
      ] ff

let po = function
  | OVar o -> pl @@ ovar_name o
  | OConst f -> pl @@ string_of_float f

let pp_owner_ante (o,c,f) =
  let rel = match c with
    | `Ge -> ">="
    | `Gt -> ">"
    | `Eq -> "="
  in
  pg rel [
    po o;
    plift @@ string_of_float f
  ]

let pp_constraint ff { env; ante; conseq; owner_ante; pc } =
  let gamma = SM.bindings env in
  let context_vars = init !KCFA.cfa (fun i -> Printf.sprintf "(%s Int)" @@ ctxt_var i) in
  let free_vars = "(NU Int)":: context_vars @ (gamma |> List.map (fun (v,_) -> Printf.sprintf "(%s Int)" v)) in
  let denote_gamma = List.map (fun (v,t) ->
      match t with
      | `Int r -> pp_refine r v
      | _ -> (fun _ -> ())
    ) gamma in
  let denote_path = List.map (fun (v1,v2) ->
      match SM.find v1 env,SM.find v2 env with
      | `Int _,`Int _ -> psl ["="; v1; v2]
      | _ -> (fun _ -> ())
    ) pc in
  let oante = List.map pp_owner_ante owner_ante in
  let e_assum = denote_path @ oante @ denote_gamma in
  pg "assert" [
    pg "forall" [
      print_string_list free_vars;
      pg "=>" [
        pg "and" ((pp_refine ante "NU")::e_assum);
        pp_refine conseq "NU"
      ]
    ]
  ] ff;
  pp_print_cut ff ()

let pp_oconstraint ff ocon =
  begin
    match ocon with
    | Write o -> pg "assert" [
                     pg "=" [
                       po o;
                       plift "1.0"
                     ]
                   ] ff
    | Live o -> pg "assert" [
                    pg ">" [
                      po o;
                      plift "0.0"
                    ]
                  ] ff
    | Shuff ((o1,o2),(o1',o2')) ->
      pg "assert" [
          pg "=" [
            pg "+" [
              po o1;
              po o2
            ];
            pg "+" [
              po o1';
              po o2'
            ];
          ]
        ] ff
    | Split (o,(o1,o2)) ->
      pg "assert" [
          pg "=" [
            po o;
            pg "+" [
              po o1;
              po o2
            ]
          ]
        ] ff
    | Eq (o1,o2) ->
      pg "assert" [
          pg "=" [
            po o1;
            po o2
          ]
        ] ff
  end;
  pp_print_cut ff ()

let call_z3 cons =
  let (i,o) = Unix.open_process "z3 -in -T:30" in
  output_string o cons;
  output_string o "(check-sat)\n";
  close_out o;
  let res = input_line i in
  res = "sat"

let solve ~print_cons owner_cons ovars refinements arity =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  pp_open_vbox ff 0;
  IntMap.iter (fun k v ->
    pp_sexpr (fun spc ps ->
      ps "declare-fun"; spc ();
      ps @@ pred_name k; spc();
      print_string_list (init v (fun _ -> "Int")) ff;
      spc ();
      ps "Bool"
    ) ff;
    pp_print_cut ff ()
  ) arity;
  List.iter (fun ov ->
    print_string_list [ "declare-fun"; ovar_name ov; "()"; "Real" ] ff;
    pp_print_cut ff ()
  ) ovars;
  List.iter (pp_oconstraint ff) owner_cons;
  List.iter (pp_constraint ff) refinements;
  pp_close_box ff ();
  let cons = Buffer.contents buf in
  if print_cons then begin
    Printf.fprintf stderr "Sending constraints >>>\n%s\n<<<<\n to z3\n" cons; flush stderr
  end;
  call_z3 cons
