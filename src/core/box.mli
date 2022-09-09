open Sidekick_core_logic

type Const.view += private Box of Term.t

val box : Term.store -> Term.t -> Term.t
(** [box tst t] makes a new constant that "boxes" [t].
  This way it will be opaque. *)

val as_box : Term.t -> Term.t option
val is_box : Term.t -> bool
