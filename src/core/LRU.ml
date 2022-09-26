(** Basic LRU cache *)

module type KEY = sig
  type t

  include Sidekick_sigs.EQ with type t := t
  include Sidekick_sigs.HASH with type t := t
end

module type S = sig
  type key
  type 'a t

  val create : size:int -> unit -> 'a t
  val size : _ t -> int
  val max_size : _ t -> int
  val get : 'a t -> compute:(key -> 'a) -> key -> 'a
end

module Make (K : KEY) : S with type key = K.t = struct
  type key = K.t

  module H = Hashtbl.Make (K)

  type 'a bucket = {
    k: key;
    v: 'a;
    mutable prev: 'a bucket;
    mutable next: 'a bucket;
  }

  type 'a t = {
    mutable first: 'a bucket option;
    tbl: 'a bucket H.t;
    max_size: int;
  }

  let size self = H.length self.tbl
  let max_size self = self.max_size

  let create ~size () : _ t =
    { first = None; tbl = H.create (min 64 size); max_size = size }

  let move_first_ self (b : _ bucket) =
    let first =
      match self.first with
      | None -> assert false
      | Some b -> b
    in
    if first != b then (
      (* remove b *)
      b.prev.next <- b.next;
      b.next.prev <- b.prev;
      (* add b *)
      let last = first.prev in
      b.prev <- last;
      b.next <- first;
      last.next <- b;
      first.prev <- b;
      self.first <- Some b
    )

  let remove_last_ self =
    match self.first with
    | None -> assert false
    | Some first ->
      let last = first.prev in
      last.prev.next <- first;
      first.prev <- last.prev;
      H.remove self.tbl last.k

  let add_bucket self k v =
    let rec b = { k; v; prev = b; next = b } in
    H.add self.tbl k b;
    match self.first with
    | None -> self.first <- Some b
    | Some _ -> move_first_ self b

  let get (self : _ t) ~compute:f (k : key) : 'a =
    match H.find self.tbl k with
    | bucket ->
      move_first_ self bucket;
      bucket.v
    | exception Not_found ->
      let v = f k in

      (* make room, if required *)
      if H.length self.tbl = self.max_size then remove_last_ self;
      assert (H.length self.tbl < self.max_size);

      add_bucket self k v;
      v
end
