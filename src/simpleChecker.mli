val typecheck_prog: ?save_types:((int -> (SimpleTypes.r_typ StringMap.t) option) -> unit) -> SimpleTypes.funtyp StringMap.t -> Ast.prog -> SimpleTypes.funtyp StringMap.t
