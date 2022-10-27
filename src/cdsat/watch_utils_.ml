(* find a term in [w] that is not assigned, or otherwise,
   the one with highest level
   @return index of term to watch, and [true] if all are assigned *)
let rec find_watch_ tst w i highest : int * bool =
  if i = Array.length w then
    highest, true
  else if TVar.has_value tst w.(i) then (
    let highest =
      if TVar.level tst w.(i) > TVar.level tst w.(highest) then
        i
      else
        highest
    in
    find_watch_ tst w (i + 1) highest
  ) else
    i, false
