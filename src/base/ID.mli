
(* This file is free software. See file "license" for more details. *)

(** Unique Identifiers *)

(**
    We use generative identifiers everywhere in [Sidekick_base]. Unlike
    strings, there are no risk of collision: during parsing, a new
    declaration or definition should create a fresh [ID.t] and associate
    it with the string name, and later references should look into some hashtable
    or map to get the ID corresponding to a string.

    This allows us to handle definition shadowing or binder shadowing easily.
*)

type t
(** The opaque type of unique identifiers *)

val make : string -> t
(** [make s] creates a new identifier with name [s]
    and some internal information. It is different than any other identifier
    created before or after, even with the same name. *)

val makef : ('a, Format.formatter, unit, t) format4 -> 'a
(** [makef "foo %d bar %b" 42 true] is like
    [make (Format.asprintf "foo %d bar %b" 42 true)]. *)

val copy : t -> t
(** Fresh copy of the identifier, distinct from it, but with the
    same name. *)

val id : t -> int
(** Unique integer counter for this identifier. *)

val to_string : t -> string
(** Print identifier. *)

val to_string_full : t -> string
(** Printer name and unique counter for this ID. *)

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.HASH with type t := t
include Intf.PRINT with type t := t

val pp_name : t CCFormat.printer

module Map : CCMap.S with type key = t
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t

