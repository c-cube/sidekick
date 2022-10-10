type t = U_timeout | U_max_depth | U_incomplete | U_asked_to_stop

let pp out = function
  | U_timeout -> Fmt.string out {|"timeout"|}
  | U_max_depth -> Fmt.string out {|"max depth reached"|}
  | U_incomplete -> Fmt.string out {|"incomplete fragment"|}
  | U_asked_to_stop -> Fmt.string out {|"asked to stop by callback"|}
