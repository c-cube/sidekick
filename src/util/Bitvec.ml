type t = { mutable chunks: bytes (* TODO: use a in32vec with bigarray *) }

let create () : t = { chunks = Bytes.make 32 '\x00' }
let i2c = Char.chr
let c2i = Char.code

(* from index to offset in bytes *)
let[@inline] idx_bytes_ (i : int) : int = i lsr 3

(* from index to offset in a single char *)
let mask_ = 0b111

(* number of bytes *)
let[@inline] len_ (self : t) : int = Bytes.length self.chunks

let[@inline never] resize_ self idx : unit =
  let new_size =
    min Sys.max_string_length
      (max (idx + 2)
         (let l = len_ self in
          l + 10 + (l / 2)))
  in
  let new_chunks = Bytes.make new_size (i2c 0) in
  Bytes.blit self.chunks 0 new_chunks 0 (len_ self);
  self.chunks <- new_chunks;
  assert (len_ self > idx)

let[@inline] ensure_size self i =
  let idx = idx_bytes_ i in
  if idx >= len_ self then resize_ self idx

let[@inline] get self i : bool =
  let idx = idx_bytes_ i in
  let c = c2i (Bytes.get self.chunks idx) in
  c land (1 lsl (i land mask_)) <> 0

let set self i b : unit =
  let idx = idx_bytes_ i in
  let c = c2i (Bytes.get self.chunks idx) in
  let c =
    if b then
      c lor (1 lsl (i land mask_))
    else
      c land lnot (1 lsl (i land mask_))
  in
  Bytes.set self.chunks idx (i2c c)

let clear_all self = Bytes.fill self.chunks 0 (len_ self) '\x00'
