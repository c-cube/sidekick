type 'a t = { mutable data: 'a array; mutable sz: int }

let make n x = { data = Array.make n x; sz = 0 }
let[@inline] create () = { data = [||]; sz = 0 }
let[@inline] clear s = s.sz <- 0

let[@inline] shrink t i =
  assert (i >= 0);
  assert (i <= t.sz);
  t.sz <- i

let[@inline] pop_exn t =
  if t.sz = 0 then invalid_arg "vec.pop";
  let x = Array.unsafe_get t.data (t.sz - 1) in
  t.sz <- t.sz - 1;
  x

let[@inline] pop t =
  if t.sz = 0 then
    None
  else (
    let x = Array.unsafe_get t.data (t.sz - 1) in
    t.sz <- t.sz - 1;
    Some x
  )

let[@inline] size t = t.sz
let[@inline] is_empty t = t.sz = 0
let[@inline] is_full t = Array.length t.data = t.sz

let[@inline] copy t : _ t =
  let data = Array.copy t.data in
  { t with data }

let resize_ t x size =
  let arr' = Array.make size x in
  Array.blit t.data 0 arr' 0 t.sz;
  t.data <- arr';
  ()

let ensure_cap_ self x n =
  if n > Array.length self.data then (
    let new_size = max n (2 * Array.length self.data) in
    resize_ self (x ()) new_size
  )

let ensure_size_with self f n =
  ensure_cap_ self f n;
  if n > self.sz then (
    for i = self.sz to n - 1 do
      self.data.(i) <- f ()
    done;
    self.sz <- n
  )

let ensure_size self ~elt:x n = ensure_size_with self (fun () -> x) n

(* grow the array *)
let[@inline never] grow_to_double_size t x : unit =
  let new_size = min Sys.max_array_length (max 4 (2 * Array.length t.data)) in
  if new_size = t.sz then failwith "vec: cannot resize";
  resize_ t x new_size;
  assert (Array.length t.data > t.sz);
  ()

let[@inline] push t x : unit =
  if is_full t then grow_to_double_size t x;
  Array.unsafe_set t.data t.sz x;
  t.sz <- t.sz + 1

let[@inline] get t i =
  if i < 0 || i >= t.sz then invalid_arg "vec.get";
  Array.unsafe_get t.data i

let[@inline] set t i v =
  if i < 0 || i > t.sz then invalid_arg "vec.set";
  if i = t.sz then
    push t v
  else
    Array.unsafe_set t.data i v

let[@inline] fast_remove t i =
  assert (i >= 0 && i < t.sz);
  Array.unsafe_set t.data i @@ Array.unsafe_get t.data (t.sz - 1);
  t.sz <- t.sz - 1

let append ~into v : unit =
  if v.sz = 0 then
    ()
  else (
    if v.sz + into.sz > Array.length into.data then
      resize_ into v.data.(0) (v.sz + into.sz);
    Array.blit v.data 0 into.data into.sz v.sz;
    into.sz <- into.sz + v.sz
  )

let prepend v ~into : unit =
  if v.sz = 0 then
    ()
  else (
    if v.sz + into.sz > Array.length into.data then
      resize_ into v.data.(0) (v.sz + into.sz);
    Array.blit into.data 0 into.data v.sz into.sz;
    (* shift elements *)
    Array.blit v.data 0 into.data 0 v.sz;
    into.sz <- into.sz + v.sz
  )

let filter_in_place f vec =
  let i = ref 0 in
  while !i < size vec do
    if f (Array.unsafe_get vec.data !i) then
      incr i
    else
      fast_remove vec !i
  done

let sort t f : unit =
  let sub_arr =
    if is_full t then
      t.data
    else
      Array.sub t.data 0 t.sz
  in
  Array.fast_sort f sub_arr;
  t.data <- sub_arr

let iter ~f t =
  for i = 0 to size t - 1 do
    f (Array.unsafe_get t.data i)
  done

let iteri ~f t =
  for i = 0 to size t - 1 do
    f i (Array.unsafe_get t.data i)
  done

let to_iter v k = iter ~f:k v
let exists p t = Iter.exists p @@ to_iter t
let for_all p t = Iter.for_all p @@ to_iter t
let fold f acc a = Iter.fold f acc @@ to_iter a
let to_list a = Iter.to_list @@ to_iter a
let to_array a = Array.sub a.data 0 a.sz

let of_list l : _ t =
  match l with
  | [] -> create ()
  | x :: tl ->
    let v = make (List.length tl + 1) x in
    List.iter (push v) l;
    v

let pp ?(sep = ", ") pp out v =
  let first = ref true in
  iter v ~f:(fun x ->
      if !first then
        first := false
      else
        Format.fprintf out "%s@," sep;
      pp out x)
