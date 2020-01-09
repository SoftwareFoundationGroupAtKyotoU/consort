open Ppxlib

let mk_cast ~loc ty =
  [%expr (fun x -> (x :> [%t ty]))]

let () =
  let ext = Context_free.Rule.extension in
  Driver.register_transformation "ppx_cast"
    ~rules:[
      ext @@ Extension.declare
          "cast"
          Extension.Context.expression
          Ast_pattern.(ptyp __)
          (fun ~loc ~path:_ ty ->
            mk_cast ~loc ty)
    ]
