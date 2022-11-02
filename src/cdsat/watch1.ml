open Watch_utils_

type t = { vst: TVar.store; arr: TVar.t array; mutable alive: bool }

let make vst l = { alive = true; vst; arr = Array.of_list l }
let[@inline] make_a vst arr : t = { alive = true; vst; arr }
let[@inline] alive self = self.alive
let[@inline] kill self = self.alive <- false

let[@inline] iter (self : t) k =
  if Array.length self.arr > 0 then k self.arr.(0)

let init (self : t) t ~on_all_set : unit =
  let i, all_set = find_watch_ self.vst self.arr 0 0 in
  (* put watch first *)
  Util.swap_array self.arr i 0;
  TVar.add_watcher self.vst self.arr.(0) ~watcher:t;
  if all_set then on_all_set ();
  ()

let update (self : t) t ~watch ~on_all_set : Watch_res.t =
  if self.alive then (
    (* find another watch. If none is present, keep the
       current one and call [on_all_set]. *)
    assert (self.arr.(0) == watch);
    let i, all_set = find_watch_ self.vst self.arr 0 0 in
    if all_set then (
      on_all_set ();
      Watch_res.Watch_keep (* just keep current watch *)
    ) else (
      (* use [i] as the watch *)
      assert (i > 0);
      Util.swap_array self.arr i 0;
      TVar.add_watcher self.vst self.arr.(0) ~watcher:t;
      Watch_res.Watch_remove
    )
  ) else
    Watch_res.Watch_remove
