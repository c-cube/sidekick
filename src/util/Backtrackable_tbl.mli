(** {1 A backtrackable hashtable} *)

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

module Make(A : ARG) : S with type key = A.Key.t and type value = A.Value.t
