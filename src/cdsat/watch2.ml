open Watch_utils_

type t = TVar.t array

let dummy = [||]
let make = Array.of_list
let[@inline] make_a a : t = a

let[@inline] iter w k =
  if Array.length w > 0 then (
    k w.(0);
    if Array.length w > 1 then k w.(1)
  )

let init tst w t ~on_unit ~on_all_set : unit =
  let i0, all_set0 = find_watch_ tst w 0 0 in
  Util.swap_array w i0 0;
  let i1, all_set1 = find_watch_ tst w 1 0 in
  Util.swap_array w i1 1;
  TVar.add_watcher tst w.(0) ~watcher:t;
  TVar.add_watcher tst w.(1) ~watcher:t;
  assert (
    if all_set0 then
      all_set1
    else
      true);
  if all_set0 then
    on_all_set ()
  else if all_set1 then (
    assert (not (TVar.has_value tst w.(0)));
    on_unit w.(0)
  );
  ()

let update tst w t ~watch ~on_unit ~on_all_set : Watch_res.t =
  (* find another watch. If none is present, keep the
     current ones and call [on_unit] or [on_all_set]. *)
  if w.(0) == watch then
    (* ensure that if there is only one watch, it's the first *)
    Util.swap_array w 0 1
  else
    assert (w.(1) == watch);
  let i, all_set1 = find_watch_ tst w 1 0 in
  if all_set1 then (
    if TVar.has_value tst w.(0) then
      on_all_set ()
    else
      on_unit w.(0);
    Watch_res.Watch_keep (* just keep current watch *)
  ) else (
    (* use [i] as the second watch *)
    assert (i > 1);
    Util.swap_array w i 1;
    TVar.add_watcher tst w.(1) ~watcher:t;
    Watch_res.Watch_remove
  )
