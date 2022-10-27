open Watch_utils_

type t = TVar.t array

let dummy = [||]
let make = Array.of_list
let[@inline] make_a a : t = a
let[@inline] iter w k = if Array.length w > 0 then k w.(0)

let init tst w t ~on_all_set : unit =
  let i, all_set = find_watch_ tst w 0 0 in
  (* put watch first *)
  Util.swap_array w i 0;
  TVar.add_watcher tst w.(0) ~watcher:t;
  if all_set then on_all_set ();
  ()

let update tst w t ~watch ~on_all_set : Watch_res.t =
  (* find another watch. If none is present, keep the
     current one and call [on_all_set]. *)
  assert (w.(0) == watch);
  let i, all_set = find_watch_ tst w 0 0 in
  if all_set then (
    on_all_set ();
    Watch_res.Watch_keep (* just keep current watch *)
  ) else (
    (* use [i] as the watch *)
    assert (i > 0);
    Util.swap_array w i 0;
    TVar.add_watcher tst w.(0) ~watcher:t;
    Watch_res.Watch_remove
  )
