module Solver = struct
  type options = {
    timeout : int;
    command : string option;
    command_extra : string option;
  }

  let default = {
    timeout = 30;
    command = None;
    command_extra = None
  }
end
