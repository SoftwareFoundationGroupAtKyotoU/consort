open Format

type ref_init =
  | RNone
  | RInt of int
  | RVar of string

type fn_call = {
  callee: string;
  arg_names: string list;
  label: int;
}


type lhs =
  | Var of string
  | Const of int
  | Mkref of ref_init
  | Deref of string
  | Plus of string * string
  | Call of fn_call
  | Nondet

type cond =
  | Leq
  | Eq
  | Neq
  | Lt

type exp =
  | Unit
  | EVar of string
  | EInt of int
  | Cond of string * exp * exp
  | Seq of exp * exp
  | Assign of string * string
  | Let of string * lhs * exp
  | Alias of string * string
  | Assert of cond * string * string
  | ECall of fn_call


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

let pprint_lhs ff = function
  | Var x -> pprint_var ff x
  | Const i -> pprint_int ff i
  | Mkref v -> pp_print_string ff "mkref "; pprint_rinit ff v
  | Deref v -> fprintf ff "*%s" v
  | Plus (v1,v2) -> fprintf ff "%s + %s" v1 v2
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
  | Unit -> pp_print_string ff "()"
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
  | Let (var, lhs, body) ->
    pp_open_hovbox ff 1;
    fprintf ff "let %s = " var;
    pprint_lhs ff lhs;
    fprintf ff " in@;";
    pprint_expr ~force_brace:true ff body;
    pp_close_box ff ()
  | Assign (x, y) ->
    fprintf ff "%s := %s" x y
  | Cond (x,tr,fl) ->
    fprintf ff "if %s then " x;
    pprint_expr ~force_brace:true ff tr;
    fprintf ff "@;else ";
    pprint_expr ~force_brace:true ff fl
  | Alias(x,y) ->
    fprintf ff "alias(%s = %s)" x y
  | Assert(cond,x,y) ->
    fprintf ff "assert(%s " x;
    pprint_cond ff cond;
    fprintf ff " %s)" y
  | EVar v -> pprint_var ff v
  | EInt i -> pprint_int ff i
  | ECall c -> pprint_fn_call ff c

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
