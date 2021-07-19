
module type RANKED = Heap_intf.RANKED

module type S = Heap_intf.S

module Make(Elt : RANKED) = struct
  type elt_store = Elt.store
  type elt = Elt.t

  type t = {
    store : elt_store;
    heap : elt Vec.t;
  }

  let _absent_index = -1

  let create store : t =
    { store;
      heap = Vec.create(); }

  let[@inline] left i = (i lsl 1) + 1 (* i*2 + 1 *)
  let[@inline] right i = (i + 1) lsl 1 (* (i+1)*2 *)
  let[@inline] parent i = (i - 1) asr 1 (* (i-1) / 2 *)

  (*
  let rec heap_property cmp ({heap=heap} as s) i =
    i >= (Vec.size heap)  ||
      ((i = 0 || not(cmp (Vec. get heap i) (Vec.get heap (parent i))))
       && heap_property cmp s (left i) && heap_property cmp s (right i))

  let heap_property cmp s = heap_property cmp s 1
  *)

  (* [elt] is above or at its expected position. Move it up the heap
     (towards high indices) to restore the heap property *)
  let percolate_up (self:t) (elt:Elt.t) : unit =
    let pi = ref (parent (Elt.heap_idx self.store elt)) in
    let i = ref (Elt.heap_idx self.store elt) in
    while !i <> 0 && Elt.cmp self.store elt (Vec.get self.heap !pi) do
      Vec.set self.heap !i (Vec.get self.heap !pi);
      Elt.set_heap_idx self.store (Vec.get self.heap !i) !i;
      i  := !pi;
      pi := parent !i
    done;
    Vec.set self.heap !i elt;
    Elt.set_heap_idx self.store elt !i

  let percolate_down (self:t) (elt:Elt.t): unit =
    let sz = Vec.size self.heap in
    let li = ref (left (Elt.heap_idx self.store elt)) in
    let ri = ref (right (Elt.heap_idx self.store elt)) in
    let i = ref (Elt.heap_idx self.store elt) in
    begin
      try
        while !li < sz do
          let child =
            if !ri < sz && Elt.cmp self.store (Vec.get self.heap !ri) (Vec.get self.heap !li)
            then !ri
            else !li
          in
          if not (Elt.cmp self.store (Vec.get self.heap child) elt) then raise_notrace Exit;
          Vec.set self.heap !i (Vec.get self.heap child);
          Elt.set_heap_idx self.store (Vec.get self.heap !i) !i;
          i  := child;
          li := left !i;
          ri := right !i
        done;
      with Exit -> ()
    end;
    Vec.set self.heap !i elt;
    Elt.set_heap_idx self.store elt !i

  let[@inline] in_heap self x = Elt.heap_idx self.store x >= 0

  let[@inline] decrease self x = assert (in_heap self x); percolate_up self x

  (*
  let increase cmp s n =
    assert (in_heap s n); percolate_down cmp s (V.get s.indices n)
  *)

  let filter (self:t) filt : unit =
    let j = ref 0 in
    let lim = Vec.size self.heap in
    for i = 0 to lim - 1 do
      if filt (Vec.get self.heap i) then (
        Vec.set self.heap !j (Vec.get self.heap i);
        Elt.set_heap_idx self.store (Vec.get self.heap i) !j;
        incr j;
      ) else (
        Elt.set_heap_idx self.store (Vec.get self.heap i) _absent_index;
      );
    done;
    Vec.shrink self.heap (lim - !j);
    for i = (lim / 2) - 1 downto 0 do
      percolate_down self (Vec.get self.heap i)
    done

  let size s = Vec.size s.heap

  let is_empty s = Vec.is_empty s.heap

  let clear self : unit =
    Vec.iter (fun e -> Elt.set_heap_idx self.store e _absent_index) self.heap;
    Vec.clear self.heap;
    ()

  let insert self elt =
    if not (in_heap self elt) then (
      Elt.set_heap_idx self.store elt (Vec.size self.heap);
      Vec.push self.heap elt;
      percolate_up self elt;
    )

  (*
  let update cmp s n =
    assert (heap_property cmp s);
    begin
      if in_heap s n then
        begin
          percolate_up cmp s (Vec.get s.indices n);
          percolate_down cmp s (Vec.get s.indices n)
        end
      else insert cmp s n
    end;
    assert (heap_property cmp s)
  *)

  let remove_min self =
    match Vec.size self.heap with
    | 0 -> raise Not_found
    | 1 ->
      let x = Vec.pop self.heap in
      Elt.set_heap_idx self.store x _absent_index;
      x
    | _ ->
      let x = Vec.get self.heap 0 in
      let new_hd = Vec.pop self.heap in (* heap.last() *)
      Vec.set self.heap 0 new_hd;
      Elt.set_heap_idx self.store x _absent_index;
      Elt.set_heap_idx self.store new_hd 0;
      (* enforce heap property again *)
      if Vec.size self.heap > 1 then (
        percolate_down self new_hd;
      );
      x

end [@@inline]
