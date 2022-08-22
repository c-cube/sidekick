type ('a, 'b) handler = 'a -> 'b
type ('a, 'b) t = { h: ('a, 'b) handler Vec.t } [@@unboxed]

let nop_handler_ _ = assert false

module Emitter = struct
  type nonrec ('a, 'b) t = ('a, 'b) t

  let emit (self : (_, unit) t) x =
    if not (Vec.is_empty self.h) then
      (Vec.iter [@inlined]) self.h ~f:(fun h -> h x)

  let emit_collect (self : _ t) x : _ list =
    if Vec.is_empty self.h then
      []
    else (
      let l = ref [] in
      Vec.iter self.h ~f:(fun h -> l := h x :: !l);
      !l
    )

  let emit_iter self x ~f =
    if not (Vec.is_empty self.h) then
      Vec.iter self.h ~f:(fun h ->
          let y = h x in
          f y)

  let create () : _ t = { h = Vec.make 3 nop_handler_ }
end

let on self ~f = Vec.push self.h f
let of_emitter x = x
let emit = Emitter.emit
let emit_collect = Emitter.emit_collect
let emit_iter = Emitter.emit_iter
