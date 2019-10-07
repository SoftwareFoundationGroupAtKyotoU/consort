type t = {
  proc_stdout: in_channel;
  proc_stderr: in_channel;
  proc_stdin: out_channel;
  proc_out_descr: Unix.file_descr;
  pid: int;
}

let spawn ?env cmd =
  let env = Option.value ~default:(Unix.environment ()) env in
  let ((out,stdin,err) as ch) = Unix.open_process_full cmd env in
  let pid = Unix.process_full_pid ch in
  {
    proc_stdout = out;
    proc_stdin = stdin;
    proc_stderr = err;
    proc_out_descr = Unix.descr_of_in_channel out;
    pid
  }

let dispose ?(kill=true) t =
  close_in t.proc_stdout;
  close_in t.proc_stderr;
  begin
    if kill then begin
      (if Sys.unix then
         ignore @@ Sys.command @@ Printf.sprintf "pkill -P %d" t.pid);
      Unix.kill t.pid Sys.sigkill
    end
  end;
  ignore @@ Unix.waitpid [] t.pid

let select_pool ~timeout ~prock ~acc ~finish p =
  let in_map = Hashtbl.create 10 in
  let in_descr =
    List.map (fun (p,ready,disp) ->
      let descr = p.proc_out_descr in
      Hashtbl.add in_map descr (p,ready,disp);
      descr
    ) p
  in
  let rec loop ~acc waiting =
    match waiting with
    | [] -> finish acc
    | _ ->
      let (ready,_,_) = Unix.select
          waiting
          []
          []
          (float timeout)
      in
      let new_waiting = List.filter (fun e -> not @@ List.mem e ready) waiting in
      let destroy_from_descr d =
        let (p,_,disp) = Hashtbl.find in_map d in
        dispose p;
        disp ()
      in
      let cleanup rest =
        List.iter destroy_from_descr rest;
        List.iter destroy_from_descr new_waiting
      in
      let rec process_results a = function
        | [] ->
          loop ~acc:a new_waiting
        | h::t ->
          let (_,cb,_) = Hashtbl.find in_map h in
          let r = cb () in
          begin
            match prock acc r with
            | `Return v -> cleanup t; v
            | `Continue acc' ->
              process_results acc' t
          end
      in
      process_results acc ready
  in
  loop ~acc in_descr
