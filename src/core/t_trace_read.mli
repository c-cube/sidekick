open Sidekick_core_logic
module Tr = Sidekick_trace

type term_ref = Tr.entry_id
type t

val create : source:Tr.Source.t -> Term.store -> t
val read_term : t -> term_ref -> (Term.t, string) result
