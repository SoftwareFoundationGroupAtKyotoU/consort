open Format
open Sexplib.Std

type ref_contents =
  | RNone
  | RInt of int
  | RVar of string

type ref_init = ref_contents
  
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
  | Call of fn_call
  | Deref of string
  | Tuple of ref_contents list
  | Nondet

type patt =
  | PVar of string
  | PTuple of patt list
  | PNone

type relation = {
  rop1: imm_op;
  cond: string;
  rop2: imm_op
}

type ap =
  | AVar of string
  | ADeref of ap
  | AProj of ap * int

type exp =
  | EVar of string
  | Cond of int * string * exp * exp
  | Seq of exp * exp
  | Assign of string * imm_op * exp
  | Let of int * patt * lhs * exp
  | Alias of int * string * ap * exp
  | Assert of relation * exp

type fn = { name: string; args: (string list); body: exp }

type prog = fn list * exp

let ps s ff = pp_print_string ff s

let pprint_var = ps

let pf f v ff = fprintf ff f v
let pl l ff = List.iter (fun f -> f ff) l
let pv = pprint_var

let pprint_int i ff = fprintf ff "%d" i
let pi = pprint_int

let indent_from_here ff = pp_open_vbox ff 2
let dedent ff = pp_close_box ff ()
let nl ff = pp_print_cut ff ()
let newline = nl
let semi ff = ps ";" ff; nl ff
let null _ = ()
let rec psep sep l ff = match l with
  | [] -> ()
  | [h] -> h ff
  | h::t -> h ff; ps sep ff; psep sep t ff

let pprint_fn_call { callee; arg_names; label } ff =
  fprintf ff "%s:%d(%s)" callee label @@ String.concat ", " arg_names

let pp_rinit = function
  | RNone -> ps "_"
  | RVar v -> pv v
  | RInt i -> pprint_int i

let pp_imm = function
  | IInt i -> pprint_int i
  | IVar v -> pv v

let pprint_kv (k,v) =
  pl [
    pf "%s: " k;
    pp_rinit v
  ]

let pp_lhs = function
  | Var x -> pv x
  | Const i -> pi i
  | Mkref il -> pl [
                    ps "mkref ";
                    pp_rinit il
                  ]
  | Tuple rinit ->
    pl [
        ps "(";
        psep ", " @@ List.map pp_rinit rinit;
        ps ")"
      ]
  | Deref v -> pl [
                   ps "*";
                   pv v
                 ]
  | Call c -> pprint_fn_call c
  | Nondet -> ps "_"

let rec pp_patt = function
  | PVar v -> pv v
  | PNone -> ps "_"
  | PTuple l -> pl [
                    ps "(";
                    psep ", " @@ List.map pp_patt l;
                    ps ")"
                  ]

let rec pp_ap = function
  | AVar v -> pv v
  | ADeref ap -> pl [ ps "*"; pp_ap ap ]
  | AProj (ap,ind) -> pl [ pp_ap ap; ps "."; pi ind ]

let rec pp_expr e =
  match e with
  | Seq (e1, e2) ->
    pl [
        maybe_brace e1;
        semi;
        pp_expr e2
      ]
  | Let (id, patt, lhs, body) ->
    maybe_brace ~all_seq:true ~pre:(pl [
          pf "let:%d " id;
          pp_patt patt;
          ps " = ";
          pp_lhs lhs;
          ps " in ";
      ]) body
  | Assign (x, y, e) ->
    pl [
        pf "%s := " x; pp_imm y;
        semi;
        pp_expr e
      ]
  | Cond (id,x,tr,fl) ->
    pl [
      indent_from_here;
      (fun ff -> fprintf ff "if:%d %s then {" id x); newline;
      pp_expr tr; dedent; newline;
      indent_from_here; ps "} else {"; newline;
      pp_expr fl; dedent; newline; ps "}"
    ]
  | Alias(id,x,y,e) ->
    pl [
        pf "alias:%d(" id;
        pv x;
        ps " = ";
        pp_ap y;
        ps ")";
        semi;
        pp_expr e
      ]
  | Assert ({ rop1; cond; rop2 },e) ->
    pl [
        ps "assert(";
        pp_imm rop1;
        pf " %s " cond;
        pp_imm rop2;
        ps ")"; semi;
        pp_expr e
      ]
  | EVar v -> pv v
and maybe_brace ?(all_seq=false) ?pre e : formatter -> unit =
  let need_block = 
      match e with
      | Seq _ -> true
      | Alias _ when all_seq -> true
      | Assert _ when all_seq -> true
      | Assign _ when all_seq -> true
      | _ -> false
  in
  if need_block then
    pl [
      indent_from_here;
      (match pre with Some f -> f | None -> null);
      ps "{"; newline;
      pp_expr e; dedent; newline;
      ps "}"
    ]
  else
    pl [
      (match pre with
        Some f -> pl [ f; newline ]
      | None -> null);
      pp_expr e
    ]

let pprint_fn ff {name; args; body} =
  let open Format in begin
    pl [
      indent_from_here;
      (fun ff -> fprintf ff "%s(%s) " name @@ String.concat ", " args);
      ps "{"; newline;
      pp_expr body;
      dedent; newline; ps "}"
    ] ff;
    pp_force_newline ff ()
  end

let pprint_prog ff (fn,body) =
  List.iter (pprint_fn ff) fn;
  pp_open_vbox ff 1;
  fprintf ff "{@;";
  pp_expr body ff;
  pp_close_box ff ();
  pp_force_newline ff (); pp_print_string ff "}"

let pretty_print_gen printer x =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  printer ff x;
  Format.pp_print_flush ff ();
  Buffer.contents buf

let pretty_print_program = pretty_print_gen pprint_prog
let pretty_print_expr = pretty_print_gen (fun ff e -> pp_expr e ff)
let pretty_print_fn = pretty_print_gen pprint_fn
