open Format

type t = { ff: Format.formatter; buf: Buffer.t }

let pp_sexpr printer { ff; _ } =
  pp_open_box ff 2;
  pp_print_string ff "(";
  printer (pp_print_space ff) (fun s -> pp_print_string ff s);
  pp_print_string ff ")";
  pp_close_box ff ()

let rec iter_print ~spc pf l = match l with
  | [] -> ()
  | [h] -> pf h
  | h::t -> pf h; spc (); iter_print ~spc pf t

let rec init i f =
  if i = 0 then []
  else (f i)::(init (i - 1) f)

let print_string_list l ff =
  pp_sexpr (fun spc ps ->
    iter_print ~spc ps l
  ) ff

let psl = print_string_list

let print_generic head l ff =
  pp_sexpr (fun spc ps ->
    ps head; spc ();
    iter_print ~spc (fun susp -> susp ff) l
  ) ff

let pg = print_generic

let plift s { ff; _ } = pp_print_string ff s
let pl = plift

let break { ff; _ } = pp_print_cut ff ()

let atom { ff; _ } = pp_print_string ff

let to_string { buf; _ } = Buffer.contents buf

let to_channel { buf; _ } c =
  Buffer.output_buffer c buf

let finish { ff; _ } =
  pp_print_flush ff ()

let fresh () =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  pp_open_vbox ff 0;
  { ff; buf }
                                             
