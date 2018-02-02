
open Solver_types

type t = Lit.t list

val make : Lit.t list -> t
val lits : t -> Lit.t list
val iter : (Lit.t -> unit) -> t -> unit
val to_seq : t -> Lit.t Sequence.t
val pp : t Fmt.printer

module Tbl : CCHashtbl.S with type key = t
