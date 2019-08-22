open Ppxlib
open Ast_builder.Default

let expand_with expr =
  let loc = expr.pexp_loc in
  match expr.pexp_desc with
  | Pexp_let (Nonrecursive, [ vb ], e) ->
    let fn = pexp_fun ~loc Nolabel None vb.pvb_pat e in
    pexp_apply ~loc
      (pexp_ident ~loc @@ Located.mk ~loc @@ Ldot (Lident "Let_syntax", "mwith"))
      [ Nolabel, vb.pvb_expr; Labelled "f", fn ]
  | _ ->
    Location.raise_errorf
      ~loc
      "'%%with' can only be used with a non-recursive 'let' and a single binding"

let () =
  Driver.register_transformation "with_monad"
    ~extensions:[
      Extension.declare
        "with"
        Extension.Context.expression
        Ast_pattern.(single_expr_payload __)
        (fun ~loc:_ ~path:_ expr ->
          expand_with expr)
    ]