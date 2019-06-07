open Sexplib.Std

type bif_refine_t = [
    `Unconstrained
  | `BifPred of string
][@@deriving sexp]

type bif_arg_t = bif_refine_t RefinementTypes._typ [@@deriving sexp]

type bif_t = {
  arg_types: bif_arg_t list;
  output_types: bif_arg_t list;
  result_type: bif_arg_t;
}[@@deriving sexp]

type bif_env_t = bif_t StringMap.t
let bif_env_t_of_sexp = StringMap.t_of_sexp ~v:bif_t_of_sexp

let lift_type t =
  let r_orig = RefinementTypes.get_refinement t in
  let r = match r_orig with
    | `Unconstrained -> RefinementTypes.True
    | `BifPred t -> RefinementTypes.BuiltInPred t
  in
  RefinementTypes.update_refinement r t

let load_built_in_types f =
  let parsed = Sexplib.Sexp.load_sexp f |> bif_env_t_of_sexp in
  StringMap.map (fun {arg_types; output_types; result_type } ->
    {
      RefinementTypes.arg_types = List.map lift_type arg_types;
      RefinementTypes.output_types = List.map lift_type output_types;
      RefinementTypes.result_type = lift_type result_type
    }
  ) parsed
  
