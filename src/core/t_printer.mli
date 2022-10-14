(** Extensible printer for {!Sidekick_core_logic.Term.t} *)

type term = Sidekick_core_logic.Term.t

type hook = recurse:term Fmt.printer -> Fmt.t -> term -> bool
(** Printing hook, responsible for printing certain subterms *)

module Hooks : sig
  type t

  val empty : t
  val add : hook -> t -> t
end

val default_hooks : Hooks.t ref

val pp_with : Hooks.t -> term Fmt.printer
(** Print using the hooks *)

val pp : term Fmt.printer
(** Print using {!default_hooks} *)

val pp_limit : max_depth:int -> max_nodes:int -> term Fmt.printer
(** Print with a limit on the number of nodes printed. An ellipsis is
    displayed otherwise. *)
