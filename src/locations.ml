let string_of_location p =
  let open Lexing in
  (* This is a workaround for an (apparently) ludicrous bug in Menhir *)
  let t = Obj.repr p in
  if Obj.is_block t then
    Printf.sprintf
      "line %d, col %d in file %s"
      p.pos_lnum
      (p.pos_cnum - p.pos_bol)
      p.pos_fname
  else begin
    print_endline @@ string_of_int @@ Obj.obj t;
    "<!!INVALID LOC>"
  end

let sexp_of_location p =
  let open Lexing in
  let open Sexplib.Std in
  let t = Obj.repr p in
  let p =
    if Obj.is_block t then
      p
    else
      Lexing.dummy_pos
  in
  [%sexp_of: (string * int * int * int)] (p.pos_fname, p.pos_lnum, p.pos_bol, p.pos_cnum)

let location_of_sexp s =
  let open Lexing in
  let open Sexplib.Std in
  let pos_fname, pos_lnum, pos_bol, pos_cnum = [%of_sexp: string * int * int * int] s in
  { pos_fname; pos_lnum; pos_bol; pos_cnum }
  
let set_file_name lexbuf in_name lnum = 
  let open Lexing in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = in_name; pos_lnum = lnum };
  lexbuf.lex_start_p <- { lexbuf.lex_start_p with pos_fname = in_name; pos_lnum = lnum }

let raise_errorf ~loc p =
  Printf.ksprintf (fun txt ->
    failwith @@ (string_of_location loc) ^ ": " ^ txt
  ) p
