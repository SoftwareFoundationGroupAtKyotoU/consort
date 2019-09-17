let string_of_location p =
  let open Lexing in
  (* This is a workaround for an (apparently) ludicrous bug in Menhir *)
  let t = Obj.repr p in
  if Obj.is_block t then
    Printf.sprintf
      "In file %s, line %d, col %d"
      p.pos_fname
      p.pos_lnum
      (p.pos_cnum - p.pos_bol)
  else "<!!INVALID LOC>"
    

let set_file_name lexbuf in_name lnum = 
  let open Lexing in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = in_name; pos_lnum = lnum };
  lexbuf.lex_start_p <- { lexbuf.lex_start_p with pos_fname = in_name; pos_lnum = lnum }

let raise_errorf ~loc p =
  Printf.ksprintf (fun txt ->
    failwith @@ (string_of_location loc) ^ ": " ^ txt
  ) p
