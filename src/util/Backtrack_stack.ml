type 'a t = { vec: 'a Vec.t; lvls: int Vec.t }

let create () : _ t = { vec = Vec.create (); lvls = Vec.create () }
let[@inline] n_levels self : int = Vec.size self.lvls
let[@inline] push self x : unit = Vec.push self.vec x

let[@inline] push_if_nonzero_level self x : unit =
  if n_levels self > 0 then Vec.push self.vec x

let[@inline] push_level (self : _ t) : unit =
  Vec.push self.lvls (Vec.size self.vec)

let pop_levels (self : _ t) (n : int) ~f : unit =
  if n > n_levels self then
    Error.errorf "Backtrack_stack.pop_levels %d (size: %d)" n (n_levels self);
  if n > 0 then (
    let new_lvl = n_levels self - n in
    let i = Vec.get self.lvls new_lvl in
    while Vec.size self.vec > i do
      let x = Vec.pop_exn self.vec in
      f x
    done;
    Vec.shrink self.lvls new_lvl
  )

let iter ~f self = Vec.iter ~f self.vec
