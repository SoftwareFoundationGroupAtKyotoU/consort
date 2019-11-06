include ExternalFileBackend.Make(struct
    let strat = "(check-sat)"
    let spawn ~command ~timeout =
      Printf.sprintf "%s -t %d"
        (Option.value ~default:"hoice" command)
        timeout
    let name = "hoice"
  end)
