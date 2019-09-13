open Intrinsics
open Sexplib.Std

let ind_pred = "(define-fun valid-ind ((ind Int) (len Int)) Bool
  (and (>= ind 0) (=> (> len 0) (< ind len))))
"

let binop,relop,alias_op =
  let arg1 = "x1" in
  let arg2 = "x2" in
  let out = "out" in
  let binary_types =
    let open SexpPrinter in
    List.map (fun nm -> pg nm [ pl "Int" ]) [ out; arg1; arg2 ]
    |> ll
  in
  let in_out_type = [ RefinementTypes.Int `Unconstrained; RefinementTypes.Int `Unconstrained ] in
  let module SP = struct
    include SexpPrinter
    let arg1 = pl arg1
    let arg2 = pl arg2
    let out = pl out
  end in
  let gen_ty sym out_pred =
    sym,{
      arg_types = in_out_type;
      output_types = in_out_type;
      result_type = Int (`BifPred (out_pred,[0;1]))
    }
  in
  let binop' ?sat_sym sym out_pred (ty_acc,def_acc) : (string * bif_t) list * ((Sexplib0.Sexp.t -> unit) -> unit) list =
    let ty = gen_ty sym out_pred in
    let z3_sym = match sat_sym with
      | None -> sym
      | Some p -> p
    in
    let def =
      let open SP in
      let fun_body = pg "=" [
          out;
          pg z3_sym [
            arg1;
            arg2
          ]
        ]
      in
      pg "define-fun" [
        pl out_pred;
        binary_types;
        pl "Bool";
        fun_body
      ]
    in
    (ty::ty_acc,def::def_acc)
  in
  let relop' sym (ty_acc,def_acc) : (string * bif_t) list * ((Sexplib0.Sexp.t -> unit) -> unit) list =
    let out_pred = Printf.sprintf "rel-%s-out" sym in
    let ty = gen_ty sym out_pred in
    let def =
      let open SP in
      let fun_body = pg "ite" [
          pg sym [ arg1; arg2 ];
          pg "=" [ out; pl "0" ];
          pg "=" [ out; pl "1" ]
        ]
      in
      pg "define-fun" [
        pl out_pred;
        binary_types;
        pl "Bool";
        fun_body
      ]
    in
    ty::ty_acc,def::def_acc
  in
  binop',relop',fun sym def_name (ty_acc,def_acc) ->
    (gen_ty sym def_name)::ty_acc,def_acc

let nrel id = (id,id)

let (ty_def,defn) =
  ([],[])
  |> binop "+" "plus-+-out"
  |> binop "-" "minus---out"
  |> binop "*" "times-*-out"
  |> binop ~sat_sym:"mod" "%" "mod-%-out"
  |> relop "="
  |> relop "<="
  |> relop "<"
  |> relop ">"
  |> relop ">="
  |> alias_op "&&" "plus-+-out"
  |> alias_op "||" "times-*-out"

let () =
  let package = (
    StringMap.of_bindings ty_def,
    StringMap.of_bindings [
      nrel "<";
      nrel "=";
      nrel "<=";
      nrel ">";
      nrel ">=";
      nrel "=";
      ("!=", "uneq");
    ],
    Sys.argv.(2)
  ) in
  let output_name = Sys.argv.(1) in
  let smt_name = Filename.concat (Filename.dirname output_name) Sys.argv.(2) in
  let intr_f = open_out output_name in
  [%sexp_of: (bif_env_t * rel_interp_t * string)] package
  |> Sexplib.Sexp.output_hum intr_f;
  output_char intr_f '\n';
  let smt_out = open_out smt_name in
  let dump_sexp k =
    k (fun x ->
      Sexplib.Sexp.output_hum smt_out x;
      output_char smt_out '\n'
    )
  in
  List.iter dump_sexp defn;
  let open SexpPrinter in
  dump_sexp @@ pg "define-fun" [
    pl "uneq";
    ll [
      ll [ pl "x1"; pl "Int" ];
      ll [ pl "x2"; pl "Int" ]
    ];
    pl "Bool";
    pg "not" [
      pg "=" [
        pl "x1"; pl "x2"
      ]
    ]
    ];
  output_string smt_out ind_pred;
  flush smt_out;
  flush intr_f;
  close_out smt_out;
  close_out intr_f
