module type S = sig
  type key
  type 'a t

  val create : ?size:int -> unit -> 'a t

  val find : 'a t -> key -> 'a
  (** @raise Not_found if the key is not present *)

  val get : 'a t -> key -> 'a option
  val mem : _ t -> key -> bool
  val length : _ t -> int
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val to_iter : 'a t -> (key * 'a) Iter.t
  val add : 'a t -> key -> 'a -> unit
  val remove : _ t -> key -> unit
  val push_level : _ t -> unit
  val pop_levels : _ t -> int -> unit
  val n_levels : _ t -> int
end

module type ARG = sig
  type t

  val equal : t -> t -> bool
  val hash : t -> int
end

module Make (A : ARG) = struct
  type key = A.t

  module M = CCHashtbl.Make (A)
  module BS = Backtrack_stack

  type 'a undo_op = Add of key * 'a | Remove of key
  type 'a t = { tbl: 'a M.t; undo: 'a undo_op BS.t }

  let create ?(size = 32) () : _ t =
    { tbl = M.create size; undo = BS.create () }

  let apply_undo self u =
    match u with
    | Add (k, v) -> M.replace self.tbl k v
    | Remove k -> M.remove self.tbl k

  let[@inline] find (self : _ t) k = M.find self.tbl k
  let[@inline] get (self : _ t) k : _ option = M.get self.tbl k
  let[@inline] mem self k = M.mem self.tbl k
  let[@inline] length self = M.length self.tbl
  let[@inline] iter f self = M.iter f self.tbl
  let[@inline] push_level self = BS.push_level self.undo

  let[@inline] pop_levels self n =
    BS.pop_levels self.undo n ~f:(apply_undo self)

  let[@inline] n_levels self = BS.n_levels self.undo

  let add self k v : unit =
    if BS.n_levels self.undo > 0 then (
      try
        let old_v = M.find self.tbl k in
        BS.push self.undo (Add (k, old_v))
      with Not_found -> BS.push self.undo (Remove k)
    );
    M.replace self.tbl k v

  let remove self k : unit =
    if BS.n_levels self.undo > 0 then (
      try
        (* get value to restore it *)
        let v = M.find self.tbl k in
        M.remove self.tbl k;
        BS.push self.undo (Add (k, v))
      with Not_found -> ()
    ) else
      M.remove self.tbl k

  let[@inline] to_iter self yield = M.iter (fun k v -> yield (k, v)) self.tbl
end
