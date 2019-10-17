open SexpPrinter

type ownership =
    OVar of int
  | OConst of float

type ocon =
  (* Constraint ownership variable n to be 1 *)
  | Write of ownership
  (* ((r1, r2),(r1',r2')) is the shuffling of permissions s.t. r1 + r2 = r1' + r2' *)
  | Shuff of (ownership * ownership) * (ownership * ownership)
  | Split of ownership * (ownership * ownership)
  | Eq of ownership * ownership
  (* For well-formedness: if o1 = 0, then o2 = 0 *)
  | Wf of ownership * ownership
  (* Ge o1 >= o2 *)
  | Ge of ownership * ownership

let owner_fact = 0.02

let pred = Printf.sprintf
"(define-fun ov-wf ((o Real) (m Int)) Bool
  (and (<= o 1) (<= 0 o) (= o (* %f m))))" owner_fact

let ovar_name ovar = Printf.sprintf "ovar-%d" ovar
let mult_name o_name = o_name ^ "-mult"
let ovar_mult ovar = mult_name @@ ovar_name ovar

type options = Solver.options
let default = Solver.default

let ownership_arg_gen = Solver.opt_gen ~nm:"o" ~solv_nm:"ownership solver"

let pp_wf o_buf i =
  pg "assert" [
    pg "ov-wf" [
      pl @@ ovar_name i;
      pl @@ ovar_mult i
    ]
  ] o_buf.printer;
  break o_buf

let print_owner_decl ovars ff =
  List.iter (fun ov ->
    print_string_list [ "declare-const"; ovar_name ov; "Real" ] ff.printer;
    break ff
  ) ovars

let po : ownership -> (Sexplib.Sexp.t -> 'a) -> 'a = function
  | OVar o -> pl @@ ovar_name o
  | OConst f -> pl @@ string_of_float f

let pp_oconstraint ff ocon =
  begin
    match ocon with
    | Write o -> pg "assert" [
                     pg "=" [
                       po o;
                       plift "1.0"
                     ]
                   ]
    | Shuff ((o1,o2),(o1',o2')) ->
      begin
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
        ] ff.printer;
        break ff;
        pg "assert" [
          pg "<=" [
            pg "+" [
              po o1;
              po o2
            ];
            pl "1.0"
          ]
        ]
      end
    | Split (o,(o1,o2)) ->
      pg "assert" [
          pg "=" [
            po o;
            pg "+" [
              po o1;
              po o2
            ]
          ]
        ]
    | Eq (o1,o2) ->
      pg "assert" [
          pg "=" [
            po o1;
            po o2
          ]
        ]
    | Ge (o1,o2) ->
      pg "assert" [
          pg ">=" [
            po o1;
            po o2
          ]
        ]
    | Wf (o1,o2) ->
      pg "assert" [
          pg "=>" [
            pg "=" [ po o1; pl "0.0" ];
            pg "=" [ po o2; pl "0.0" ]
          ]
        ]
  end ff.printer;
  break ff

let print_ownership_constraints ovars ocons sexp_buf =
  print_owner_decl ovars sexp_buf;
  List.iter (pp_oconstraint sexp_buf) ocons
let rec extract_assoc m acc =
  let open Sexplib.Sexp in
  match m with
  | (List 
      (
        Atom "define-fun"::
          Atom nm::
          (List [])::
          Atom ty::body
      ))::l ->
    extract_assoc l @@ (nm,ty,body)::acc
  | _::l -> extract_assoc l acc
  | [] -> acc
    
let solve_ownership ~opts ?save_cons (ovars,ocons) =
  let o_buf = SexpPrinter.fresh () in
  print_ownership_constraints ovars ocons o_buf;
  atom o_buf.printer pred;
  break o_buf;
  let live_count = List.map (fun ov ->
    pg "ite" [
      pg "=" [ pl @@ ovar_mult ov; pl "0" ];
      pl "0";
      pl "1"
    ]) ovars in

  List.iter (fun i ->
    pg "declare-const" [
      pl @@ ovar_mult i;
      pl "Int"
    ] o_buf.printer;
    break o_buf
  ) ovars;
  List.iter (pp_wf o_buf) ovars;
  if (List.length live_count > 0) then begin
    pg "maximize" [
      pg "+" live_count
    ] o_buf.printer
  end;
  finish o_buf;
  let res = Z3Channel.call_z3_raw ~opts ?save_cons ~debug_cons:false ~defn_file:None ~strat:"(check-sat)" ~get_model:true o_buf in
  match res with
  | Solver.Sat Some m ->
    begin
      let open Sexplib.Sexp in
      let s = scan_sexp @@ Lexing.from_string m in
      match s with
      | List (Atom "model"::model) ->
        let model_assoc = extract_assoc model [] in
        let mult_val = (List.fold_left (fun acc (nm,ty,body) ->
            match ty,body with
            | "Int",[Atom s] ->
              (nm,(int_of_string s) |> float |> (( *. ) owner_fact))::acc
            | _ -> acc)) [] model_assoc in
        Some (List.map (fun o_var ->
            (o_var,List.assoc (ovar_mult o_var) mult_val)
        ) ovars)
      | _ -> None
    end
  | _ -> None

