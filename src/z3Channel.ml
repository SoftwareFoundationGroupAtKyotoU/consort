module Ch = SolverChannel.Make(struct
    let name = "z3"
    let base_command = "z3 -in -T:30"
  end)
    
(* remove one of these *)
let call_z3_raw = Ch.call
let call_z3 = Ch.call

