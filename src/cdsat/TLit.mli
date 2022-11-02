(** Literal for {!TVar.t} *)

type t = { var: TVar.t; sign: bool }

val make : bool -> TVar.t -> t
val neg : t -> t
val abs : t -> t
val sign : t -> bool
val var : t -> TVar.t
val pp : TVar.store -> t Fmt.printer
