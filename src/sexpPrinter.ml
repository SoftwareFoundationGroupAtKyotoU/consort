open Format

type t = { printer: Sexplib.Sexp.t -> unit; ff: Format.formatter; buf: Buffer.t }

let rec iter_print l (ff: Sexplib.Sexp.t list -> 'a) : 'a  = match l with
  | [] -> ff []
  | h::t ->
    h (fun at ->
        iter_print t (fun pl -> ff @@ at::pl))

let rec init i f =
  if i = 0 then []
  else (f i)::(init (i - 1) f)

let print_generic head l (ff: Sexplib.Sexp.t -> 'a) : 'a =
  iter_print l (fun pl ->
    ff @@ Sexplib.Sexp.List ((Sexplib.Sexp.Atom head)::pl)
  )

let pg = print_generic

let plift s ff = ff @@ Sexplib.Sexp.Atom s
let pl : string -> (Sexplib.Sexp.t -> 'a) -> 'a = plift

let ll l ff = iter_print l (fun k ->
    ff @@ Sexplib.Sexp.List k
  )

let print_string_list l ff =
  iter_print (List.map pl l) (fun pl -> ff @@ Sexplib.Sexp.List pl)

let psl : string list -> (Sexplib.Sexp.t -> 'a) -> 'a = print_string_list


let break { ff; _ } = pp_print_cut ff ()

let atom ff s =  ff @@ Sexplib.Sexp.Atom s

let to_string { buf; _ } = Buffer.contents buf

let to_channel { buf; _ } c =
  Buffer.output_buffer c buf

let finish { ff; _ } =
  pp_print_flush ff ()

let rec pp_sexp_on t ff =
  let open PrettyPrint in
  match t with
  | Sexplib.Sexp.List l ->
    pb [
        ps "(";
        psep_gen sbrk @@ List.map pp_sexp_on l;
        ps ")"
      ] ff
  | Sexplib.Sexp.Atom s -> ps s ff

let mk_printer ff =
  (fun t ->
    pp_sexp_on t ff)

let fresh () =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  pp_open_vbox ff 0;
  { printer = mk_printer ff; ff; buf }
