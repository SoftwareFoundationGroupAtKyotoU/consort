type log_filter =
  | None
  | All
  | Subset of Std.StringSet.t

  type log_level = Level of int
let level_debug = Level 0
and level_warn = Level 1
and level_none = Level 2

let level = ref level_none

let set_level lvl = level := lvl

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
  let Level lvl = !level in
  if (check_source src) && lvl <= 1 then
    match src with
    | Some w -> Printf.eprintf ("Debug: [%s] " ^^ fmt ^^ "\n%!") w
    | None -> Printf.eprintf ("Debug: " ^^ fmt ^^ "\n%!")
  else
    Printf.ifprintf stderr fmt

let warn ?src fmt = 
  let Level lvl = !level in
  if (check_source src) && lvl <= 2 then
    match src with
    | Some w -> Printf.eprintf ("Warn: [%s] " ^^ fmt ^^ "\n%!") w
    | None -> Printf.eprintf ("Warn: " ^^ fmt ^^ "\n%!")
  else
    Printf.ifprintf stderr fmt

module type LocatedD = sig
  val debug : ('a, out_channel, unit) format -> 'a
  val warn : ('a, out_channel, unit) format -> 'a
end

module Located(W : sig val where : string end) : LocatedD = struct
  let debug fmt = debug ~src:W.where fmt
  let warn fmt = warn ~src:W.where fmt
end

let located ~where =
  let module L = Located(struct let where = where end) in
  (module L : LocatedD)
