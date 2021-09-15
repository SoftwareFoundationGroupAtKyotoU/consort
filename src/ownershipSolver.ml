open SexpPrinter

type ownership = OwnershipInference.ownership

let pred = "(define-fun ov-wf ((o Real)) Bool
  (and (<= o 1) (<= 0 o)))" 

let ovar_name ovar = Printf.sprintf "ovar-%d" ovar

let pp_wf o_buf i =
  pg "assert" [
    pg "ov-wf" [
      pl @@ ovar_name i;
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
    let open OwnershipInference in
    match ocon with
    | Write o -> pg "assert" [
                     pg "=" [
                       po o;
                       plift "1.0"
                     ]
                   ]
    | Live o -> pg "assert" [
                    pg ">" [
                      po o;
                      plift "0.0"
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

let rec interp_real sexp =
  let open Std.OptionMonad in
  let open Sexplib.Sexp in
  match sexp with
  | Atom s ->
    Float.of_string_opt s
  | List [Atom "/"; v1; v2] ->
    let* e1 = interp_real v1 in
    let* e2 = interp_real v2 in
    Some (e1 /. e2)
  | _ -> None

let solve_ownership ~opts result =
  let open OwnershipInference.Result in
  let ovars = result.ovars in
  let ocons = result.ocons in
  let max_vars = result.max_vars in
  let o_buf = SexpPrinter.fresh () in
  print_ownership_constraints ovars ocons o_buf;
  atom o_buf.printer pred;
  break o_buf;
  let live_count =
    Std.IntSet.elements max_vars
    |> List.map (fun ov ->
        pg "ite" [
          pg ">" [ pl @@ ovar_name ov; pl "0." ];
          pl "1";
          pl "0"
        ])
  in
  List.iter (pp_wf o_buf) ovars;
  if (List.length live_count > 0) then begin
    pg "maximize" [
      pg "+" live_count
    ] o_buf.printer
  end;
  finish o_buf;
  let res =
    let opts : ArgOptions.t = {
      opts with
      show_model = true;
      intrinsics_file = None;
    } in
    Z3Channel.call_z3_raw
      ~opts
      ~strat:"(check-sat)"
      o_buf in
  match res with
  | Solver.Sat Some m ->
    begin
      let open Sexplib.Sexp in
      let s = scan_sexp @@ Lexing.from_string m in
      match s with
      | List (Atom "model" :: model) | List model ->
        let model_assoc = extract_assoc model [] in
        let o_sigma = List.fold_left (fun acc (nm,ty,body) ->
            match ty,body with
            | "Real",[term] ->
              interp_real term
              |> Option.fold ~none:acc ~some:(fun o ->
                  (nm,o)::acc
                )
            | _ -> acc) [] model_assoc
        in
        let open Std.OptionMonad in
        List.fold_left (fun oacc o_var ->
            let* acc = oacc in
            let* v = List.assoc_opt (ovar_name o_var) o_sigma in
            Some ((o_var,v)::acc)
          ) (Some []) ovars
      | _ -> None
    end
  | _ -> None
