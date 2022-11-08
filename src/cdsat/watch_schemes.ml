type watch_update_res =
  | Watch_keep  (** Keep the watch *)
  | Watch_remove  (** Remove the watch *)

(* find a term in [w] that is not assigned, or otherwise,
   the one with highest level
   @return index of term to watch, and [true] if all are assigned *)
let find_watch_ tst w ~idx0 : int * bool =
  let rec loop i idx_with_highest_level =
    if i = Array.length w then
      idx_with_highest_level, true
    else if TVar.has_value tst w.(i) then (
      let idx_with_highest_level =
        if TVar.level tst w.(i) > TVar.level tst w.(idx_with_highest_level) then
          i
        else
          idx_with_highest_level
      in
      loop (i + 1) idx_with_highest_level
    ) else
      i, false
  in
  loop idx0 0

module Make (Ev : sig
  type t
end) =
struct
  type handle = int

  module Handle_v_map = TVar.Dense_map (struct
    type t = Veci.t

    let create () = Veci.create ~cap:2 ()
  end)

  type watch =
    | No_watch
    | Watch1 of { ev: Ev.t; arr: TVar.t array }
    | Watch2 of { ev: Ev.t; arr: TVar.t array }

  type t = {
    vst: TVar.store;
    watches: watch Vec.t;
    by_var: Handle_v_map.t;
        (** maps a variable to the handles of its watchers *)
    alive: Bitvec.t;
    free_slots: Veci.t;
  }

  let create vst : t =
    {
      vst;
      watches = Vec.create ();
      by_var = Handle_v_map.create ();
      alive = Bitvec.create ();
      free_slots = Veci.create ();
    }

  type cb_ = unit:bool -> Ev.t -> unit

  (* allocate new watch *)
  let make_watch_ (self : t) (w : watch) : handle =
    if Veci.is_empty self.free_slots then (
      let h = Vec.size self.watches in
      Vec.push self.watches w;
      Bitvec.ensure_size self.alive (h + 1);
      Bitvec.set self.alive h true;
      h
    ) else (
      let h = Veci.pop self.free_slots in
      Bitvec.set self.alive h true;
      Vec.set self.watches h w;
      h
    )

  (* [h] is currently watching [v] *)
  let set_watch (self : t) (v : TVar.t) (h : handle) : unit =
    let vec = Handle_v_map.get self.by_var v in
    Veci.push vec h

  let watch1 (self : t) (arr : TVar.t array) (ev : Ev.t) ~(f : cb_) : handle =
    let h = make_watch_ self (Watch1 { arr; ev }) in
    let i, all_set = find_watch_ self.vst arr ~idx0:0 in
    (* put watched var first *)
    Util.swap_array arr i 0;
    set_watch self arr.(0) h;
    if all_set then f ~unit:false ev;
    h

  let watch2 (self : t) (arr : TVar.t array) (ev : Ev.t) ~(f : cb_) : handle =
    let h = make_watch_ self (Watch2 { arr; ev }) in
    (* put watched vars first *)
    let i0, all_set0 = find_watch_ self.vst arr ~idx0:0 in
    Util.swap_array arr i0 0;
    let i1, all_set1 = find_watch_ self.vst arr ~idx0:1 in
    Util.swap_array arr i1 1;
    set_watch self arr.(0) h;
    set_watch self arr.(1) h;
    assert (
      if all_set0 then
        all_set1
      else
        true);
    if all_set0 then
      f ~unit:false ev
    else if all_set1 then (
      assert (not (TVar.has_value self.vst arr.(0)));
      f ~unit:true ev
    );
    h

  (** disable watch. It will be removed from watchers next time they
      are updated or next time {!gc} is called. *)
  let kill (self : t) (h : handle) : unit =
    if Bitvec.get self.alive h then (
      Vec.set self.watches h No_watch;
      Bitvec.set self.alive h false
    )

  let[@inline] alive (self : t) (h : handle) : bool = Bitvec.get self.alive h

  let gc (self : t) : unit =
    (* first, filter all dead watches from [self.by_var] *)
    Handle_v_map.iter self.by_var ~f:(fun _v handles ->
        Veci.filter_in_place (alive self) handles);
    (* then, mark the dead watch slots for reuse *)
    Vec.iteri self.watches ~f:(fun i _w ->
        if not (alive self i) then Veci.push self.free_slots i)

  (* update a single watch *)
  let update1 (self : t) (h : handle) (w : watch) ~updated_var ~f :
      watch_update_res =
    match w with
    | No_watch -> Watch_remove
    | _ when not (alive self h) -> Watch_remove
    | Watch1 { arr; ev } ->
      (* find another watch. If none is present, keep the
         current one and call [f]. *)
      assert (TVar.equal arr.(0) updated_var);
      let i, all_set = find_watch_ self.vst arr ~idx0:0 in
      if all_set then (
        f ~unit:false ev;
        Watch_keep (* just keep current watch *)
      ) else (
        (* use [i] as the watch *)
        assert (i > 0);
        Util.swap_array arr i 0;
        set_watch self arr.(0) h;
        Watch_remove
      )
    | Watch2 { arr; ev } ->
      (* find another watch. If none is present, keep the
         current ones and call [f]. *)
      if TVar.equal arr.(0) updated_var then
        (* ensure that if there is only one watch, it's the first *)
        Util.swap_array arr 0 1
      else
        assert (TVar.equal arr.(1) updated_var);
      let i, all_set1 = find_watch_ self.vst arr ~idx0:1 in
      if all_set1 then (
        if TVar.has_value self.vst arr.(0) then
          f ~unit:false ev
        else
          f ~unit:true ev;
        (* just keep current watch *)
        Watch_keep
      ) else (
        (* use [i] as the second watch *)
        assert (i > 1);
        Util.swap_array arr i 1;
        set_watch self arr.(1) h;
        Watch_remove
      )

  let update (self : t) (v : TVar.t) ~(f : cb_) : unit =
    let vec = Handle_v_map.get self.by_var v in
    let i = ref 0 in
    while !i < Veci.size vec do
      let handle = Veci.get vec !i in
      let w = Vec.get self.watches handle in
      match update1 self handle w ~updated_var:v ~f with
      | Watch_keep -> incr i
      | Watch_remove -> Veci.fast_remove vec !i
    done
end
