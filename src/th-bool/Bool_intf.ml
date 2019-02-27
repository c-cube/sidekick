
(** {1 Signatures for booleans} *)

type 'a view =
  | B_not of 'a
  | B_and of 'a IArray.t
  | B_or of 'a IArray.t
  | B_imply of 'a IArray.t * 'a
  | B_atom of 'a

(** {2 Interface for a representation of boolean terms} *)
module type BOOL_TERM = sig
  type t
  type state

  val equal : t -> t -> bool
  val hash : t -> int

  val view_as_bool : t -> t view
  (** View a term as a boolean formula *)

  val make : state -> t view -> t
  (** Build a boolean term from a formula view *)
end
