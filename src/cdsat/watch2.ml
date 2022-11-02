open Watch_utils_

type t = { vst: TVar.store; arr: TVar.t array; mutable alive: bool }

let dummy = [||]
let make vst l : t = { alive = true; vst; arr = Array.of_list l }
let[@inline] make_a vst arr : t = { vst; arr; alive = true }
let[@inline] alive self = self.alive
let[@inline] kill self = self.alive <- false

let[@inline] iter (self : t) k =
  if Array.length self.arr > 0 then (
    k self.arr.(0);
    if Array.length self.arr > 1 then k self.arr.(1)
  )

let init (self : t) t ~on_unit ~on_all_set : unit =
  let i0, all_set0 = find_watch_ self.vst self.arr 0 0 in
  Util.swap_array self.arr i0 0;
  let i1, all_set1 = find_watch_ self.vst self.arr 1 0 in
  Util.swap_array self.arr i1 1;
  TVar.add_watcher self.vst self.arr.(0) ~watcher:t;
  TVar.add_watcher self.vst self.arr.(1) ~watcher:t;
  assert (
    if all_set0 then
      all_set1
    else
      true);
  if all_set0 then
    on_all_set ()
  else if all_set1 then (
    assert (not (TVar.has_value self.vst self.arr.(0)));
    on_unit self.arr.(0)
  );
  ()

let update (self : t) t ~watch ~on_unit ~on_all_set : Watch_res.t =
  if self.alive then (
    (* find another watch. If none is present, keep the
       current ones and call [on_unit] or [on_all_set]. *)
    if self.arr.(0) == watch then
      (* ensure that if there is only one watch, it's the first *)
      Util.swap_array self.arr 0 1
    else
      assert (self.arr.(1) == watch);
    let i, all_set1 = find_watch_ self.vst self.arr 1 0 in
    if all_set1 then (
      if TVar.has_value self.vst self.arr.(0) then
        on_all_set ()
      else
        on_unit self.arr.(0);
      Watch_res.Watch_keep (* just keep current watch *)
    ) else (
      (* use [i] as the second watch *)
      assert (i > 1);
      Util.swap_array self.arr i 1;
      TVar.add_watcher self.vst self.arr.(1) ~watcher:t;
      Watch_res.Watch_remove
    )
  ) else
    Watch_res.Watch_remove
