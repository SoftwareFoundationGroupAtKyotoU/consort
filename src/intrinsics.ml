open Sexplib.Std

type bif_arg_t = RefinementTypes.typ [@@deriving sexp]

type bif_t = {
  arg_types: bif_arg_t list;
  output_types: bif_arg_t list;
  result_type: bif_arg_t;
}[@@deriving sexp]

type bif_env_t = bif_t StringMap.t
let bif_env_t_of_sexp = StringMap.t_of_sexp ~v:bif_t_of_sexp
let sexp_of_bif_env_t = StringMap.sexp_of_t ~v:sexp_of_bif_t
        
(* just a mapping of connectives onto Z3 functions *)
type rel_interp_t = string StringMap.t
let rel_interp_t_of_sexp = StringMap.t_of_sexp ~v:string_of_sexp
let sexp_of_rel_interp_t = StringMap.sexp_of_t ~v:sexp_of_string

type interp_t = {
  op_interp: RefinementTypes.funtype StringMap.t;
  rel_interp: rel_interp_t;
  def_file: string option
}


let load f =
  let (op,rel,rel_defn) = Sexplib.Sexp.load_sexp f |> [%of_sexp: (bif_env_t * rel_interp_t * string)] in
  let mapped = StringMap.map (fun {arg_types; output_types; result_type } ->
      {
        RefinementTypes.arg_types = arg_types;
        RefinementTypes.output_types = output_types;
        RefinementTypes.result_type = result_type
      }
    ) op in
  let defn = Filename.concat (Filename.dirname f) rel_defn in  {
    op_interp = mapped;
    rel_interp = rel;
    def_file = Some defn
  }
  

let empty = {
  op_interp = StringMap.empty;
  rel_interp = StringMap.empty;
  def_file = None
}

let option_loader () =
  let open Arg in
  let f_name = ref None in
  [
    "-intrinsics", String (fun x -> f_name := Some x), "Load definitions of standard operations from <file>"
  ], (fun () ->
    match !f_name with
    | None -> empty
    | Some s -> load s
  )
