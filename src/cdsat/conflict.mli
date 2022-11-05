(** Conflict discovered during search *)

type t = { vst: TVar.store; lit: TLit.t; propagate_reason: Reason.t }

include Sidekick_sigs.PRINT with type t := t

val make : TVar.store -> lit:TLit.t -> propagate_reason:Reason.t -> unit -> t
