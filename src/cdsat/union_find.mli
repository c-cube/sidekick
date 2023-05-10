(** Union find *)

open Sidekick_core

type t

val create : unit -> t
(** New UF *)

val merge : t -> Term.t -> Term.t -> Reason.t -> unit
(** Merge two terms *)

val find : t -> Term.t -> Term.t
(** Current representative of this term *)

val are_equal : t -> Term.t -> Term.t -> bool

val on_changed : t -> (Term.t, unit) Event.t
(** Event firing for each term whose representative changed. *)

type expl = { merges: (Term.t * Term.t * Reason.t) list }

val pp_expl : expl Fmt.printer

val explain_equal : t -> Term.t -> Term.t -> expl
(** [explain_equal uf t u] returns an explanation of why [t = u].
    @raise Error.Error if the terms are not equal. *)

val iter_classes : t -> (Term.t * Term.t Iter.t) Iter.t
(** Iterate on equivalence classes. *)

include Sidekick_sigs.BACKTRACKABLE0 with type t := t
