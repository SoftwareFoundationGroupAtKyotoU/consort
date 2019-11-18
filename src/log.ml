type log_filter =
  | None
  | All
  | Subset of Std.StringSet.t

let sources = ref None

let all () = sources := All
let disable () = sources := None
let filter d =
  sources := Subset (Std.StringSet.of_list d)

let check_source w =
  match w,!sources with
  | _,None -> false
  | _,All -> true
  | Some w,Subset s -> Std.StringSet.mem w s
  | None, Subset _ -> false

let debug ?src fmt =
  if (check_source src) then
    match src with
    | Some w -> Printf.eprintf ("[%s] " ^^ fmt ^^ "\n%!") w
    | None -> Printf.eprintf (fmt ^^ "\n%!")
  else
    Printf.ifprintf stderr fmt

module type LocatedD = sig
  val debug : ('a, out_channel, unit) format -> 'a
end

module Located(W : sig val where : string end) : LocatedD = struct
  let debug fmt = debug ~src:W.where fmt
end

let located ~where =
  let module L = Located(struct let where = where end) in
  (module L : LocatedD)
