open Format

let pf = dprintf

let ps s ff = pp_print_string ff s

let pprint_var = ps

let pl l ff = List.iter (fun f -> f ff) l
let pv = pprint_var

let pb l =
  pl [
    (fun ff -> pp_open_box ff 1);
    pl l;
    (fun ff -> pp_close_box ff ())
  ]

let pprint_int i ff = fprintf ff "%d" i
let pi = pprint_int

let indent_from_here ff = pp_open_vbox ff 2
let dedent ff = pp_close_box ff ()
let nl ff = pp_print_cut ff ()
let newline = nl
let semi ff = ps ";" ff; nl ff
let null _ = ()
let sbrk ff = pp_print_space ff ()
let rec psep_gen sep l ff = match l with
  | [] -> ()
  | [h] -> h ff
  | h::t -> h ff; sep ff; psep_gen sep t ff
let psep sep = psep_gen (ps sep)

let pblock ?(nl=false) ~op ~body ~close =
  pl [
    pl [
      indent_from_here;
      op;
      newline
    ];
    body; dedent; newline;
    close; (if nl then newline else null)
  ]

let ul f ff v = f v ff

let pretty_print_gen printer x =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  printer ff x;
  Format.pp_print_flush ff ();
  Buffer.contents buf

let pretty_print_gen_rev printer x =
  pretty_print_gen (fun ff x -> printer x ff) x

let pp_gen_rev = pretty_print_gen_rev
let pp_gen = pretty_print_gen
