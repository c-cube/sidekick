(** Values *)

type t = Term.t

include Sidekick_sigs.EQ_ORD_HASH_PRINT with type t := t
