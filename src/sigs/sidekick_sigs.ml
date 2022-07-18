(* This file is free software. See file "license" for more details. *)

module type EQ = sig
  type t

  val equal : t -> t -> bool
end

module type ORD = sig
  type t

  val compare : t -> t -> int
end

module type HASH = sig
  type t

  val hash : t -> int
end

type 'a printer = Format.formatter -> 'a -> unit

module type PRINT = sig
  type t

  val pp : t printer
end

module type EQ_HASH_PRINT = sig
  include EQ
  include HASH with type t := t
  include PRINT with type t := t
end

module type EQ_ORD_HASH_PRINT = sig
  include EQ
  include ORD with type t := t
  include HASH with type t := t
  include PRINT with type t := t
end

module type DYN_BACKTRACKABLE = sig
  val n_levels : unit -> int
  (** Number of levels *)

  val push_level : unit -> unit
  (** Push a backtracking point *)

  val pop_levels : int -> unit
  (** [pop_levels n] removes [n] levels *)
end

module type BACKTRACKABLE0 = sig
  type t

  val n_levels : t -> int
  (** Number of levels *)

  val push_level : t -> unit
  (** Push a backtracking point *)

  val pop_levels : t -> int -> unit
  (** [pop_levels st n] removes [n] levels *)
end

module type BACKTRACKABLE1 = sig
  type 'a t

  val n_levels : _ t -> int
  (** Number of levels *)

  val push_level : _ t -> unit
  (** Push a backtracking point *)

  val pop_levels : _ t -> int -> unit
  (** [pop_levels st n] removes [n] levels *)
end

module type BACKTRACKABLE1_CB = sig
  include BACKTRACKABLE1

  val pop_levels : 'a t -> int -> f:('a -> unit) -> unit
  (** [pop_levels st n ~f] removes [n] levels, calling [f] on every removed item *)
end
