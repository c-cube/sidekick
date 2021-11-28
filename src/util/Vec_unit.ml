
type elt = unit

(* no need to store anything so we don't even provide an actual vector
   since unit is a "zero sized type" as rustaceans would say. *)
type t = {
  mutable size: int;
}

let create ?cap:_ () : t = { size=0 }
let clear self = self.size <- 0
let copy {size} = {size}
let get (_self:t) _ = ()
let size self = self.size
let iter ~f:_ (_self:t) = ()
let iteri ~f:_ (_self:t) = ()
let is_empty self = self.size = 0
let push (self:t) _ = self.size <- 1 + self.size
let fast_remove (self:t) _ = self.size <- self.size - 1
let ensure_size (self:t) i = self.size <- max self.size i
let set _ _ _ = ()
let pop self = self.size <- self.size - 1; ()
let filter_in_place _ _ = ()
let shrink (self:t) i = self.size <- i
let to_iter self k = for _i=0 to self.size - 1 do k () done
let to_array self = Iter.to_array (to_iter self)
let fold_left f acc self = Iter.fold f acc (to_iter self)
let pp ppx out self = Iter.pp_seq ppx out (to_iter self)
