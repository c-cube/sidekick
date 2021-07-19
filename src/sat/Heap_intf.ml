
module type RANKED = sig
  type store
  type t

  val heap_idx : store -> t -> int
  (** Index in heap. return -1 if never set *)

  val set_heap_idx : store -> t -> int -> unit
  (** Update index in heap *)

  val cmp : store -> t -> t -> bool
end

module type S = sig
  type elt_store

  type elt
  (** Type of elements *)

  type t
  (** Heap of {!elt}, whose priority is increased or decreased
      incrementally (see {!decrease} for instance) *)

  val create : elt_store -> t
  (** Create a heap *)

  val decrease : t -> elt -> unit
  (** [decrease h x] decreases the value associated to [x] within [h] *)

  val in_heap : t -> elt -> bool

  (*val increase : (int -> int -> bool) -> t -> int -> unit*)

  val size : t -> int
  (** Number of integers within the heap *)

  val is_empty : t -> bool

  val clear : t -> unit
  (** Clear the content of the heap *)

  val insert : t -> elt -> unit
  (** Insert a new element into the heap *)

  (*val update : (int -> int -> bool) -> t -> int -> unit*)

  val remove_min : t -> elt
  (** Remove and return the integer that has the lowest value from the heap
      @raise Not_found if the heap is empty *)

  val filter : t -> (elt -> bool) -> unit
  (** Filter out values that don't satisfy the predicate *)
end
