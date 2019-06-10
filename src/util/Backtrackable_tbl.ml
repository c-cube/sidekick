module type S = sig
  type key
  type value
  type t

  val create : ?size:int -> unit -> t

  val find : t -> key -> value
  (** @raise Not_found if the key is not present *)

  val get : t -> key -> value option
  val mem : t -> key -> bool
  val length : t -> int
  val iter : (key -> value -> unit) -> t -> unit
  val to_iter : t -> (key * value) Iter.t
  val add : t -> key -> value -> unit
  val remove : t -> key -> unit
  val push_level : t -> unit
  val pop_levels : t -> int -> unit
end

module type ARG = sig
  module Key : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
  end
  module Value : sig
    type t
    val equal : t -> t -> bool
  end
end

module Make(A : ARG) = struct
  type key = A.Key.t
  type value = A.Value.t
  module M = CCHashtbl.Make(A.Key)
  module BS = Backtrack_stack

  type undo_op = Add of key * value | Remove of key
  type t = {
    tbl: value M.t;
    undo: undo_op BS.t;
  }

  let create ?(size=32) () : t = { tbl=M.create size; undo=BS.create() }

  let apply_undo self u =
    match u with
    | Add (k,v) -> M.replace self.tbl k v
    | Remove k -> M.remove self.tbl k

  let[@inline] find (self:t) k : value = M.find self.tbl k
  let[@inline] get (self:t) k : value option = M.get self.tbl k
  let[@inline] mem self k = M.mem self.tbl k
  let[@inline] length self = M.length self.tbl
  let[@inline] iter f self = M.iter f self.tbl
  let[@inline] push_level self = BS.push_level self.undo
  let[@inline] pop_levels self n = BS.pop_levels self.undo n ~f:(apply_undo self)

  let add self k v : unit =
    if BS.n_levels self.undo > 0 then (
      try
        let old_v = M.find self.tbl k in
        BS.push self.undo (Add (k,old_v))
      with Not_found ->
        BS.push self.undo (Remove k)
    );
    M.replace self.tbl k v

  let remove self k : unit =
    if BS.n_levels self.undo > 0 then (
      try
        (* get value to restore it *)
        let v = M.find self.tbl k in
        M.remove self.tbl k;
        BS.push self.undo (Add (k,v));
      with Not_found -> ()
    ) else (
      M.remove self.tbl k
    )

  let[@inline] to_iter self yield = M.iter (fun k v -> yield (k,v)) self.tbl
end
