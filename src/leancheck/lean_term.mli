module Level = Sidekick_cic_lib.Level

type binder = BD | BI | BS | BC

type t =
  | Sort of Level.t
  | BVar of int
  | Const of string * Level.t list
  | App of t * t
  | Lam of binder * string * t * t
  | Pi of binder * string * t * t

val dummy : t
val pp : t Fmt.printer
