open Sidekick_core
module Tr = Sidekick_trace

type Tr.entry_view += Assert of Term.t | Assert_clause of Lit.t list

class t :
  Tr.Sink.t
  -> object
       inherit Term.Tracer.t

       method emit_assert_term : Term.t -> Tr.Entry_id.t
       (** Emit an assertion *)

       method emit_assert_clause : Lit.t list -> Tr.Entry_id.t
       (** Emit an assertion *)
     end

val assert_term : #t -> Term.t -> Tr.Entry_id.t
val assert_term' : #t -> Term.t -> unit
val assert_clause : #t -> Lit.t list -> Tr.Entry_id.t
val assert_clause' : #t -> Lit.t list -> unit
