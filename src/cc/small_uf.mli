(** Small union find.

    No backtracking nor explanations.
*)

open Sidekick_core

type t
(** An instance of the congruence closure. Mutable *)

val create : unit -> t

val clear : t -> unit
(** Fully reset the state *)

val merge : t -> Term.t -> Term.t -> unit
val same_class : t -> Term.t -> Term.t -> bool
