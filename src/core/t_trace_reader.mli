open Sidekick_core_logic
module Tr = Sidekick_trace
module Dec = Ser_decode

type term_ref = Tr.entry_id
type const_decoders = Const.decoders
type t

val create :
  ?const_decoders:const_decoders list -> source:Tr.Source.t -> Term.store -> t

val add_const_decoders : t -> const_decoders -> unit
val read_term : t -> term_ref -> (Term.t, string) result
