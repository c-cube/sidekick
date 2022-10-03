(** Read trace *)

open Sidekick_core
module Tr = Sidekick_trace

type entry = Assert of Term.t | Assert_clause of { id: int; c: Lit.t list }

val pp_entry : entry Fmt.printer

type t

val create :
  ?const_decoders:Const.decoders list -> Term.store -> Tr.Source.t -> t

val add_const_decoders : t -> Const.decoders -> unit
val decode : t -> tag:string -> Ser_value.t -> entry option
val decode_entry : t -> Tr.Entry_id.t -> entry option
