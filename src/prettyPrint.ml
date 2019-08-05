open Format

let pf =
  let open CamlinternalFormatBasics in
  let open CamlinternalFormat in
  let rec pprint_acc = function
    | Acc_formatting_lit (p, (Break (_, width, offset))) ->
      (fun ff ->
        pprint_acc p ff;
        pp_print_break ff width offset)
    | Acc_formatting_lit (p, fmting_lit) ->
      let s = string_of_formatting_lit fmting_lit in
      (fun ff ->
        pprint_acc p ff;
        pp_print_string ff s)
    | Acc_formatting_gen (p, Acc_open_tag acc') ->
      (fun ff ->
        pprint_acc p ff;
        pp_print_string ff "@{";
        pprint_acc acc' ff)
    | Acc_formatting_gen (p, Acc_open_box acc') ->
      (fun ff ->
        pprint_acc p ff;
        pp_print_string ff "@[";
        pprint_acc acc' ff)
    | Acc_string_literal (p, s)
    | Acc_data_string (p, s)   ->
      (fun ff ->
        pprint_acc p ff;
        pp_print_string ff s)
    | Acc_char_literal (p, c)
    | Acc_data_char (p, c)     ->
      (fun ff ->
        pprint_acc p ff;
        pp_print_char ff c)
    | Acc_delay (p, f)         ->
      (fun ff ->
        pprint_acc p ff;
        (f ()) ff)
    | Acc_flush p              ->
      (fun ff ->
        pprint_acc p ff)
    | Acc_invalid_arg (p, msg) ->
      (fun ff ->
        pprint_acc p ff; invalid_arg msg)
    | End_of_acc               -> (fun _ff -> ())
  in
  fun (Format (fmt,_)) ->
    make_printf (fun acc ->
      pprint_acc acc
    ) End_of_acc fmt


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

let ul f = fun () -> f

let pretty_print_gen printer x =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  printer ff x;
  Format.pp_print_flush ff ();
  Buffer.contents buf

let pretty_print_gen_rev printer x =
  pretty_print_gen (fun ff x -> printer x ff) x
