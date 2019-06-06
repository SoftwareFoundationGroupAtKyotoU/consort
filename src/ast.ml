open Format
open Sexplib.Std

type ref_init =
  | RNone
  | RInt of int
  | RVar of string

type fn_call = {
  callee: string;
  arg_names: string list;
  label: int;
}


type imm_op =
    IVar of string
  | IInt of int [@@deriving sexp]

type lhs =
  | Var of string
  | Const of int
  | Mkref of ref_init
  | Deref of string
  | Plus of imm_op * imm_op
  | Call of fn_call
  | Nondet

type cond =
  | Leq
  | Eq
  | Neq
  | Lt [@@deriving sexp]

type relation = {
  rop1: imm_op;
  cond: cond;
  rop2: imm_op
}

type exp =
  | EVar of string
  | Cond of int * string * exp * exp
  | Seq of exp * exp
  | Assign of string * imm_op * exp
  | Let of int * string * lhs * exp
  | Alias of int * string * string * exp
  | Assert of relation * exp

type fn = { name: string; args: (string list); body: exp }

type prog = fn list * exp

let pprint_var ff = fprintf ff "%s"

let pprint_int ff = fprintf ff "%d"

let pprint_fn_call ff { callee; arg_names; label } =
  fprintf ff "%s:%d(%s)" callee label @@ String.concat ", " arg_names

let pprint_rinit ff = function
  | RNone -> pp_print_string ff "_"
  | RVar v -> pprint_var ff v
  | RInt i -> pprint_int ff i

let pprint_imm_op ff = function
  | IInt i -> pprint_int ff i
  | IVar v -> pprint_var ff v

let pprint_lhs ff = function
  | Var x -> pprint_var ff x
  | Const i -> pprint_int ff i
  | Mkref v -> pp_print_string ff "mkref "; pprint_rinit ff v
  | Deref v -> fprintf ff "*%s" v
  | Plus (v1,v2) -> begin
      pprint_imm_op ff v1;
      pp_print_string ff " + ";
      pprint_imm_op ff v2
    end
  | Call c -> pprint_fn_call ff c
  | Nondet -> pp_print_string ff "*"

let cond_to_string = function
  | Leq -> "<="
  | Eq -> "="
  | Neq -> "!="
  | Lt -> "<"

let pprint_cond ff c = pp_print_string ff @@ cond_to_string c

let rec pprint_expr ~force_brace ff e =
  let local_force_brace = force_brace in
  match e with
  | Seq (e1, e2) ->
    let () =
      if local_force_brace then begin
        pp_open_vbox ff 1;
        fprintf ff "{@;"
      end else ()
    in
    let () = begin
      match e1 with
      | Seq _ -> pprint_expr ~force_brace:true ff e1
      | _ -> pprint_expr ~force_brace:false ff e1
    end in
    fprintf ff ";@;";
    pprint_expr ~force_brace:false ff e2;
    if local_force_brace then begin
      pp_print_string ff "}"; pp_close_box ff ()
    end else ()
  | Let (id,var, lhs, body) ->
    pp_open_hovbox ff 1;
    fprintf ff "let:%d %s = " id var;
    pprint_lhs ff lhs;
    fprintf ff " in@;";
    pprint_expr ~force_brace:true ff body;
    pp_close_box ff ()
  | Assign (x, y, e) ->
    fprintf ff "%s := " x;
    pprint_imm_op ff y;
    fprintf ff ";@;";
    pprint_expr ~force_brace ff e
  | Cond (id,x,tr,fl) ->
    fprintf ff "if:%d %s then " id x;
    pprint_expr ~force_brace:true ff tr;
    fprintf ff "@;else ";
    pprint_expr ~force_brace:true ff fl
  | Alias(id,x,y,e) ->
    fprintf ff "alias:%d(%s = %s)" id x y;
    fprintf ff ";@;";
    pprint_expr ~force_brace ff e
  | Assert ({ rop1; cond; rop2 },e) ->
    fprintf ff "assert(";
    pprint_imm_op ff rop1;
    pprint_cond ff cond;
    pprint_imm_op ff rop2;
    fprintf ff " )";
    fprintf ff ";@;";
    pprint_expr ~force_brace ff e
  | EVar v -> pprint_var ff v

let pprint_fn ff {name; args; body} =
  let open Format in begin
    fprintf ff "%s(%s) " name @@ String.concat ", " args;
    pprint_expr ~force_brace:true ff body;
    pp_force_newline ff ()
  end

let pprint_prog ff (fn,body) =
  List.iter (pprint_fn ff) fn;
  pp_open_vbox ff 1;
  fprintf ff "{@;";
  pprint_expr ~force_brace:false ff body;
  pp_close_box ff ();
  pp_force_newline ff (); pp_print_string ff "}"

let pretty_print_gen printer x =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  printer ff x;
  Format.pp_print_flush ff ();
  Buffer.contents buf

let pretty_print_program = pretty_print_gen pprint_prog
let pretty_print_expr = pretty_print_gen (pprint_expr ~force_brace:true)
let pretty_print_fn = pretty_print_gen pprint_fn
