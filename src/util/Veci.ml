module A = Bigarray.Array1

type int32arr = (int32, Bigarray.int32_elt, Bigarray.c_layout) A.t
type t = { mutable data: int32arr; mutable sz: int }

let mk_arr_ sz : int32arr = A.create Bigarray.int32 Bigarray.c_layout sz
let create ?(cap = 16) () : t = { sz = 0; data = mk_arr_ cap }
let[@inline] clear self = self.sz <- 0
let[@inline] shrink self n = if n < self.sz then self.sz <- n
let[@inline] size self = self.sz
let[@inline] is_empty self = self.sz = 0

let copy self =
  if size self = 0 then
    create ~cap:0 ()
  else (
    (* copy bigarray *)
    let data = mk_arr_ (size self) in
    A.blit self.data data;
    { sz = self.sz; data }
  )

let[@inline] fast_remove t i =
  assert (i >= 0 && i < t.sz);
  A.unsafe_set t.data i @@ A.unsafe_get t.data (t.sz - 1);
  t.sz <- t.sz - 1

let filter_in_place f vec =
  let i = ref 0 in
  while !i < size vec do
    if f (Int32.to_int (A.unsafe_get vec.data !i)) then
      incr i
    else
      fast_remove vec !i
  done

(* ensure capacity is [new_cap] *)
let resize_cap_ self new_cap =
  assert (A.dim self.data < new_cap);
  let new_data = mk_arr_ new_cap in
  A.blit self.data (A.sub new_data 0 (A.dim self.data));
  self.data <- new_data

let ensure_cap self (n : int) =
  if n > A.dim self.data then (
    let new_cap = max n (max 4 (A.dim self.data * 2)) in
    resize_cap_ self new_cap
  )

let ensure_size self n =
  if n > self.sz then (
    ensure_cap self n;
    self.sz <- n
  )

let[@inline] push (self : t) i : unit =
  ensure_cap self (self.sz + 1);
  self.data.{self.sz} <- Int32.of_int i;
  self.sz <- 1 + self.sz

let[@inline] push_i32 self i =
  ensure_cap self (self.sz + 1);
  self.data.{self.sz} <- i;
  self.sz <- 1 + self.sz

let[@inline] pop self =
  if self.sz > 0 then (
    let x = Int32.to_int self.data.{self.sz - 1} in
    self.sz <- self.sz - 1;
    x
  ) else
    failwith "vecI32.pop: empty"

let[@inline] get self i : int =
  assert (i >= 0 && i < self.sz);
  Int32.to_int (A.unsafe_get self.data i)

let[@inline] get_i32 self i : int32 =
  assert (i >= 0 && i < self.sz);
  A.unsafe_get self.data i

let[@inline] set self i x : unit =
  assert (i >= 0 && i < self.sz);
  A.unsafe_set self.data i (Int32.of_int x)

let[@inline] set_i32 self i x : unit =
  assert (i >= 0 && i < self.sz);
  A.unsafe_set self.data i x

let[@inline] iter ~f self =
  for i = 0 to self.sz - 1 do
    f (Int32.to_int self.data.{i})
  done

let[@inline] iteri ~f self =
  for i = 0 to self.sz - 1 do
    f i (Int32.to_int self.data.{i})
  done

let[@inline] to_iter self k = iter ~f:k self

include Vec_sig.Make_extensions (struct
  type nonrec elt = int
  type nonrec t = t

  let to_iter = to_iter
  let get = get
  let size = size
  let iter = iter
  let iteri = iteri
end)
