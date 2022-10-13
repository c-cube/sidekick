open Sidekick_core_logic
module Tr = Sidekick_trace
module Dec = Ser_decode

type term_ref = Tr.entry_id
type const_decoders = Const.decoders
type t

val create :
  ?const_decoders:const_decoders list -> source:Tr.Source.t -> Term.store -> t

val store : t -> Term.store
val add_const_decoders : t -> const_decoders -> unit
val read_term : t -> term_ref -> (Term.t, string) result
val read_term_err : t -> term_ref -> (Term.t, Ser_decode.Error.t) result

val read_term_exn : t -> term_ref -> Term.t
(** @raise Error.Error if it fails *)

val deref_term : t -> Term.t -> Term.t
(** [deref_term reader t] dereferences the root node of [t].
    If [t] is [Ref id], this returns the term at [id] instead.
    @raise Error.Error if it fails *)
