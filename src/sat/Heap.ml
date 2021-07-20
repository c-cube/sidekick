
module type RANKED = Heap_intf.RANKED

module type S = Heap_intf.S

module Make(Elt : RANKED) = struct
  type elt_store = Elt.store
  type elt = Elt.t

  type t = {
    store : elt_store;
    heap : VecI32.t; (* vec of elements *)
  }

  let _absent_index = -1

  let create store : t =
    { store;
      heap = VecI32.create(); }

  let[@inline] left i = (i lsl 1) + 1 (* i*2 + 1 *)
  let[@inline] right i = (i + 1) lsl 1 (* (i+1)*2 *)
  let[@inline] parent i = (i - 1) asr 1 (* (i-1) / 2 *)

  (*
  let rec heap_property cmp ({heap=heap} as s) i =
    i >= (VecI32.size heap)  ||
      ((i = 0 || not(cmp (Vec. get heap i) (Vec.get heap (parent i))))
       && heap_property cmp s (left i) && heap_property cmp s (right i))

  let heap_property cmp s = heap_property cmp s 1
  *)

  let[@inline] get_elt_ self i = Elt.of_int_unsafe (VecI32.get self.heap i)
  let[@inline] set_elt_ self i elt = VecI32.set self.heap i (elt:Elt.t:>int)

  (* [elt] is above or at its expected position. Move it up the heap
     (towards high indices) to restore the heap property *)
  let percolate_up (self:t) (elt:Elt.t) : unit =
    let pi = ref (parent (Elt.heap_idx self.store elt)) in
    let i = ref (Elt.heap_idx self.store elt) in
    while !i <> 0 && Elt.cmp self.store elt (get_elt_ self !pi) do
      set_elt_ self !i (get_elt_ self !pi);
      Elt.set_heap_idx self.store (get_elt_ self !i) !i;
      i  := !pi;
      pi := parent !i
    done;
    set_elt_ self !i elt;
    Elt.set_heap_idx self.store elt !i

  let percolate_down (self:t) (elt:Elt.t): unit =
    let sz = VecI32.size self.heap in
    let li = ref (left (Elt.heap_idx self.store elt)) in
    let ri = ref (right (Elt.heap_idx self.store elt)) in
    let i = ref (Elt.heap_idx self.store elt) in
    begin
      try
        while !li < sz do
          let child =
            if !ri < sz &&
               Elt.cmp self.store (get_elt_ self !ri) (get_elt_ self !li)
            then !ri
            else !li
          in
          if not (Elt.cmp self.store (get_elt_ self child) elt) then raise_notrace Exit;
          set_elt_ self !i (get_elt_ self child);
          Elt.set_heap_idx self.store (get_elt_ self !i) !i;
          i  := child;
          li := left !i;
          ri := right !i
        done;
      with Exit -> ()
    end;
    set_elt_ self !i elt;
    Elt.set_heap_idx self.store elt !i

  let[@inline] in_heap self x = Elt.heap_idx self.store x >= 0

  let[@inline] decrease self x = assert (in_heap self x); percolate_up self x

  (*
  let increase cmp s n =
    assert (in_heap s n); percolate_down cmp s (V.get s.indices n)
  *)

  let filter (self:t) filt : unit =
    let j = ref 0 in
    let lim = VecI32.size self.heap in
    for i = 0 to lim - 1 do
      if filt (get_elt_ self i) then (
        set_elt_ self !j (get_elt_ self i);
        Elt.set_heap_idx self.store (get_elt_ self i) !j;
        incr j;
      ) else (
        Elt.set_heap_idx self.store (get_elt_ self i) _absent_index;
      );
    done;
    VecI32.shrink self.heap (lim - !j);
    for i = (lim / 2) - 1 downto 0 do
      percolate_down self (get_elt_ self i)
    done

  let[@inline] size s = VecI32.size s.heap
  let[@inline] is_empty s = VecI32.is_empty s.heap

  let clear self : unit =
    VecI32.iter self.heap
      ~f:(fun e -> Elt.set_heap_idx self.store (Elt.of_int_unsafe e) _absent_index);
    VecI32.clear self.heap;
    ()

  let insert self elt =
    if not (in_heap self elt) then (
      Elt.set_heap_idx self.store elt (VecI32.size self.heap);
      VecI32.push self.heap (elt:Elt.t:>int);
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
    match VecI32.size self.heap with
    | 0 -> raise Not_found
    | 1 ->
      let x = Elt.of_int_unsafe (VecI32.pop self.heap) in
      Elt.set_heap_idx self.store x _absent_index;
      x
    | _ ->
      let x = get_elt_ self 0 in
      let new_hd = Elt.of_int_unsafe (VecI32.pop self.heap) in (* heap.last() *)
      set_elt_ self 0 new_hd;
      Elt.set_heap_idx self.store x _absent_index;
      Elt.set_heap_idx self.store new_hd 0;
      (* enforce heap property again *)
      if VecI32.size self.heap > 1 then (
        percolate_down self new_hd;
      );
      x
end [@@inline]
