
type t = VecI32.t

let create () : t = VecI32.create ~cap:16 ()

(* from index to offset in bytes *)
let[@inline] idx_in_vec_ (i:int) : int = i lsr 5

(* from index to offset in a single chunk *)
let mask_ = 0b11111

(* number of bytes *)
let[@inline] len_ (self:t) : int = VecI32.size self

let[@inline never] resize_ self idx : unit =
  let new_size =
    min Sys.max_string_length
      (max (idx+2) (let l = len_ self in l + 10 + l / 2))
  in
  VecI32.ensure_size self new_size;
  assert (len_ self > idx)

let[@inline] ensure_size self i =
  let idx = idx_in_vec_ i in
  if idx >= len_ self then (
    resize_ self idx
  )

let[@inline] get self i : bool =
  let idx = idx_in_vec_ i in
  let c = VecI32.get self idx in
  (c land (1 lsl (i land mask_))) <> 0

let set self i b : unit =
  let idx = idx_in_vec_ i in
  let c = VecI32.get self idx in
  let c =
    if b
    then c lor (1 lsl (i land mask_))
    else c land (lnot (1 lsl (i land mask_)))
  in
  VecI32.set self idx c

let clear_all self = VecI32.fill self 0

