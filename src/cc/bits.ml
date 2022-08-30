type bitfield_gen = int ref

let max_width = Sys.word_size - 2
let mk_gen () = ref 0

type t = int
type field = int

let empty : t = 0

let mk_field (gen : bitfield_gen) : field =
  let n = !gen in
  if n > max_width then Error.errorf "maximum number of CC bitfields reached";
  incr gen;
  1 lsl n

let[@inline] get field x = x land field <> 0

let[@inline] set field b x =
  if b then
    x lor field
  else
    x land lnot field

let merge = ( lor )
let equal : t -> t -> bool = CCEqual.poly
