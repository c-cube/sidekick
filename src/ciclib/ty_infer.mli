module T = Term

(** Env: definitions for constants and inductives *)
module Env : sig
  type t

  val empty : t
  val pp : t Fmt.printer

  val add_def : t -> string -> T.t -> t
  (** [add_def env name c] defines [name := c] in [env] *)

  val add_inductive : t -> Inductive.spec -> t
  (** Define an inductive *)
end

(** Stack: types for bound variables *)
module Stack : sig
  type t

  val empty : t
  val push : T.t -> t -> t
  val pp : t Fmt.printer
end

val ty_check : Env.t -> Stack.t -> T.t -> T.t
(** [ty_check env stack t] infers the type of [t] *)
