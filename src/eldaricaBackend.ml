include ExternalFileBackend.Make(struct
    let name = "eldarica"
    let spawn ~command ~timeout =
      Printf.sprintf
        "%s -t:%d -hsmt"
        (Option.value ~default:"eld" command)
        timeout
    let strat = "(check-sat)"
  end)
