let string_of_channel in_c =
  let out_buffer = Buffer.create 0x10000 in
  let buff = Bytes.create 0x1000 in
  let rec copy_loop () =
    let n = input in_c buff 0 0x1000 in
    if n = 0 then Buffer.contents out_buffer
    else
      (Buffer.add_subbytes out_buffer buff 0 n; copy_loop ())
  in
  copy_loop ()

