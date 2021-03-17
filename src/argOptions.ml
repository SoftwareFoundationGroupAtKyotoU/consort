module Solver = struct
  type options = {
    timeout : int;
    command : string option;
    command_extra : string option;
  }
end
