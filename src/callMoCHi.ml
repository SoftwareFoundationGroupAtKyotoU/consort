let call_mochi =
  let cmd = "~/git/MoCHi/src/mochi.exe ./test/to_mochi.ml" in
  let p = Process.spawn cmd in
  let res = (String.trim @@ input_line p.Process.proc_stdout, String.trim @@ input_line p.Process.proc_stderr) in
  Process.dispose p;
  res