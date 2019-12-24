open Intrinsics
open Sexplib.Std

module Sexp = Sexplib.Sexp

let () =
  let serialized = Sexp.load_sexp Sys.argv.(1) in
  let (bif,rel,defn_f) = [%of_sexp : (bif_env_t * rel_interp_t * string)] serialized in
  let defn_f = Filename.concat (Filename.dirname (Sys.argv.(1))) defn_f in
  let defns = Sexp.load_sexps defn_f in
  let flags = Sexp.load_sexp Sys.argv.(2) |> [%of_sexp: (string * int list * bool) list] in
  let (bif, defns) = List.fold_left (fun (bif, defns) (nm, flags, inv) ->
      let ty = {
        arg_types = [ RefinementTypes.Int RefinementTypes.Top ];
        output_types = [ RefinementTypes.Int RefinementTypes.Top ];
        result_type = RefinementTypes.Int (RefinementTypes.NamedPred (nm, [Paths.arg 0]))
      } in
      let bif = StringMap.add nm ty bif in
      let open SexpPrinter in
      let eqn = List.map (fun flg ->
          pg "=" [
            pl "flag";
            pl @@ string_of_int flg
          ]
        ) flags in
      let cond = pg "or" eqn in
      let (tr_branch,fl_branch) =
        if inv then
          (pl "1", pl "0")
        else
          (pl "0", pl "1")
      in
      let defn = pg "define-fun" [
          pl nm;
          ll [ ll [ pl "result"; pl "Int" ]; ll [ pl "flag"; pl "Int" ] ];
          pl "Bool";
          pg "ite" [
            cond;
            pg "=" [ pl "result"; tr_branch ];
            pg "=" [ pl "result"; fl_branch ]
          ]
        ]
      in
      let defn = defn (fun k -> k) in
      (bif, defn::defns)
    ) (bif, defns) flags in
  let output_folder = Filename.dirname Sys.argv.(3) in
  let output_defn_file = Filename.concat output_folder Sys.argv.(4) in
  let () = Sexp.save_hum Sys.argv.(3) @@ [%sexp_of: bif_env_t * rel_interp_t * string] (bif, rel, Sys.argv.(4)) in
  Sexp.save_sexps_hum output_defn_file defns
