module type CONFIG = sig
  val base_command : string
  val name : string
end


module Make(C: CONFIG) = struct
  include SolverBridge.Make(struct
      type st = in_channel
      let spawn i = i
      let prepare_out save_cons =
        let cmd = 
          match save_cons with
          | Some f_name -> Printf.sprintf "tee %s | %s" f_name C.base_command
          | None -> C.base_command
        in Unix.open_process cmd

      let dispose _ = ()
      let name = C.name
    end)
end
