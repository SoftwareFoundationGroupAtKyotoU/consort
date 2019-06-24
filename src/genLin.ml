open Intrinsics
open Sexplib.Std

let binop =
  let in_out_type = [ `Int `Unconstrained; `Int `Unconstrained ] in
  fun sym out_pred -> (sym,{
        arg_types = in_out_type;
        output_types = in_out_type;
        result_type = `Int (`BifPred out_pred)
      })

let nrel id = (id,id)

let package = (
  StringMap.of_bindings [
    binop "+" "plus-+-out";
    binop "<" "rel-<-out";
    binop "-" "minus---out"
  ],
  StringMap.of_bindings [
    nrel "<";
    nrel "=";
    nrel "<=";
    nrel ">";
    nrel ">=";
    ("!=", "not-eq")
  ],
  "lin-std.smt"
)

let () =
  [%sexp_of: (bif_env_t * rel_interp_t * string)] package
  |> Sexplib.Sexp.output_hum stdout;
  print_newline ()
