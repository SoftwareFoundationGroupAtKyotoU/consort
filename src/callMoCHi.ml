let call_mochi =
  let cmd = "~/git/MoCHi/src.mochi.exe ./test/to_mochi.ml" in
  let proc = Process.spawn cmd in
  