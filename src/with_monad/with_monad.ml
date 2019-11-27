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
      "'%%swith' can only be used with a non-recursive 'let' and a single binding"

let rec expand_do expr =
  let loc = expr.pexp_loc in
  match expr.pexp_desc with
  | Pexp_sequence (e1,e2) ->
    let e2' = expand_do e2 in
    pexp_apply ~loc
      (pexp_ident ~loc @@ Located.mk ~loc @@ Ldot (Lident "Let_syntax", "seq"))
      [ Labelled "a", e1; Labelled "b", e2']
  | _ -> expr

let wrap_value_binding nm =
  let rec lift_last expr =
    let loc = expr.pexp_loc in
    match expr.pexp_desc with
    | Pexp_fun (a,b,c,({ pexp_desc = Pexp_fun (_,_,_,_); _ } as nxt)) ->
      { expr with pexp_desc = Pexp_fun (a,b,c,lift_last nxt) }
    | Pexp_fun (_,_,_,_) ->
      pexp_apply ~loc
        (pexp_ident ~loc @@ Located.mk ~loc @@ Ldot (Lident "Let_syntax", nm))
        [ Labelled "f", expr ]
    | _ ->
      Location.raise_errorf ~loc
        "Query only lifts function definitions"
  in
  let expand_monad vb =
    match vb.pvb_expr.pexp_desc with
    | Pexp_fun (_,_,_,_) ->
      { vb with pvb_expr = lift_last vb.pvb_expr }
    | _ ->
      Location.raise_errorf
        ~loc:vb.pvb_loc
        "Query lifting expansion only supported on functions"
  in
  List.map expand_monad

let lift_defn ~loc vl nm =
  pstr_value ~loc Nonrecursive @@ wrap_value_binding nm vl

let lift_inline_defn ~loc bind body nm =
  pexp_let ~loc Nonrecursive (wrap_value_binding nm bind) body
    
let () =
  let ext = Context_free.Rule.extension in
  Driver.register_transformation "with_monad"
    ~rules:[
      ext @@ Extension.declare
          "swith"
          Extension.Context.expression
          Ast_pattern.(single_expr_payload __)
          (fun ~loc:_ ~path:_ expr ->
            expand_with expr)
    ; ext @@ Extension.declare
          "m"
          Extension.Context.expression
          Ast_pattern.(single_expr_payload __)
          (fun ~loc:_ ~path:_ expr ->
            expand_do expr)
      ; ext @@ Extension.declare
          "lq"
          Extension.Context.structure_item
          Ast_pattern.(pstr ((pstr_value nonrecursive __) ^:: nil))
          (fun ~loc ~path:_ bind ->
            lift_defn ~loc bind "proj")
      ; ext @@ Extension.declare
          "lm"
          Extension.Context.structure_item
          Ast_pattern.(pstr ((pstr_value nonrecursive __) ^:: nil))
          (fun ~loc ~path:_ bind ->
            lift_defn ~loc bind "mut")
      ; ext @@ Extension.declare
          "lm"
          Extension.Context.expression
          Ast_pattern.(pstr (pstr_eval (pexp_let nonrecursive __ __) nil ^:: nil))
          (fun ~loc ~path:_ bind body ->
            lift_inline_defn ~loc bind body "mut")
      ; ext @@ Extension.declare
          "lq"
          Extension.Context.expression
          Ast_pattern.(pstr (pstr_eval (pexp_let nonrecursive __ __) nil ^:: nil))
          (fun ~loc ~path:_ bind body ->
            lift_inline_defn ~loc bind body "proj")
    ]
