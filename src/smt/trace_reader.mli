(** Read trace *)

open Sidekick_core
module Proof = Sidekick_proof
module Tr = Sidekick_trace

type entry =
  | Assert of Term.t
  | Assert_clause of { id: int; c: Lit.t list; p: Proof.Pterm.t option }

val pp_entry : entry Fmt.printer

type t

val create :
  ?const_decoders:Const.decoders list -> Term.store -> Tr.Source.t -> t

val add_const_decoders : t -> Const.decoders -> unit
val term_trace_reader : t -> Term.Trace_reader.t
val decode : t -> tag:string -> Ser_value.t -> entry option
val decode_entry : t -> Tr.Entry_id.t -> entry option
