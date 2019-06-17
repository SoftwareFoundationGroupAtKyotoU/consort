module SMTStrategy(I: Z3BasedBackend.OV) = struct
  open Inference
  open RefinementTypes
  open SexpPrinter
  open I
  
  let po = function
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
    break ff

  let print_owner_decl ovars ff =
    List.iter (fun ov ->
      print_string_list [ "declare-const"; ovar_name ov; "Real" ] ff;
      break ff
    ) ovars
      
  let ownership _ ovars owner_cons ff =
    print_owner_decl ovars ff;
    List.iter (pp_oconstraint ff) owner_cons

  include Z3BasedBackend.StandardSolver(struct
      let strat = "(check-sat)"
    end)
end

module Backend = Z3BasedBackend.Make(SMTStrategy)

let solve = Backend.solve
