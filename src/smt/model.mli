(** Models

      A model can be produced when the solver is found to be in a
      satisfiable state after a call to {!solve}. *)

open Sigs

type t

val empty : t
val mem : t -> term -> bool
val find : t -> term -> term option
val eval : t -> term -> term option
val pp : t Fmt.printer

module Internal_ : sig
  val of_tbl : term Term.Tbl.t -> t
end
