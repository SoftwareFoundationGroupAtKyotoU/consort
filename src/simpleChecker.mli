module StringMap : Map.S with type key = string

val typecheck_prog: Ast.prog -> SimpleTypes.funtyp StringMap.t
