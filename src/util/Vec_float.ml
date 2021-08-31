
module A = Bigarray.Array1

type float_arr = (float, Bigarray.float64_elt, Bigarray.c_layout) A.t

type t = {
  mutable data: float_arr;
  mutable sz: int;
}

let mk_arr_ sz : float_arr = A.create Bigarray.float64 Bigarray.c_layout sz

let create ?(cap=16) () : t =
  { sz=0; data=mk_arr_ cap }

let[@inline] clear self = self.sz <- 0
let[@inline] shrink self n = if n < self.sz then self.sz <- n
let[@inline] size self = self.sz
let[@inline] is_empty self = self.sz = 0

let[@inline] fast_remove t i =
  assert (i>= 0 && i < t.sz);
  A.unsafe_set t.data i @@ A.unsafe_get t.data (t.sz - 1);
  t.sz <- t.sz - 1

let filter_in_place f vec =
  let i = ref 0 in
  while !i < size vec do
    if f (A.unsafe_get vec.data !i) then incr i else fast_remove vec !i
  done

(* ensure capacity is [new_cap] *)
let resize_cap_ self new_cap =
  assert (A.dim self.data < new_cap);
  let new_data = mk_arr_ new_cap in
  A.blit self.data (A.sub new_data 0 (A.dim self.data));
  self.data <- new_data

let ensure_cap self (n:int) =
  if n > A.dim self.data then (
    let new_cap = max n (A.dim self.data * 2 + 10) in
    resize_cap_ self new_cap;
  )

let ensure_size self n =
  if n > self.sz then (
    ensure_cap self n;
    self.sz <- n
  )

let[@inline] push (self:t) x : unit =
  ensure_cap self (self.sz+1);
  self.data.{self.sz} <- x;
  self.sz <- 1 + self.sz

let[@inline] pop self =
  if self.sz > 0 then (
    let x = self.data.{self.sz-1} in
    self.sz <- self.sz - 1;
    x
  ) else failwith "vec_float.pop: empty"

let[@inline] get self i : float =
  assert (i >= 0 && i < self.sz);
  A.unsafe_get self.data i

let[@inline] set self i x : unit =
  assert (i >= 0 && i < self.sz);
  A.unsafe_set self.data i x

let[@inline] iter ~f self =
  for i=0 to self.sz - 1 do
    f self.data.{i}
  done

let[@inline] iteri ~f self =
  for i=0 to self.sz - 1 do
    f i self.data.{i}
  done

let[@inline] to_iter self k = iter ~f:k self

let pp ppx out self =
  Format.fprintf out "[@[";
  iteri self
    ~f:(fun i x -> if i>0 then Format.fprintf out ",@ "; ppx out x);
  Format.fprintf out "@]]"

