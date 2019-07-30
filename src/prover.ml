type result = 
  | Unsat
  | Sat of string option
  | Timeout
  | Unhandled of string
