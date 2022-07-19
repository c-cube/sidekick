type 'a handler = 'a -> unit
type 'a t = { h: 'a handler Vec.t } [@@unboxed]

let nop_handler_ = ignore

module Emitter = struct
  type nonrec 'a t = 'a t

  let emit (self : _ t) x : unit = Vec.iter self.h ~f:(fun h -> h x)
  let create () : _ t = { h = Vec.make 3 nop_handler_ }
end

let on self ~f = Vec.push self.h f
let of_emitter x = x
let emit = Emitter.emit
