(** Explanations

      Explanations are specialized proofs, created by the congruence closure
      when asked to justify why two terms are equal. *)

open Types_

type t = Types_.explanation

include Sidekick_sigs.PRINT with type t := t

val mk_merge : E_node.t -> E_node.t -> t
(** Explanation: the nodes were explicitly merged *)

val mk_merge_t : Term.t -> Term.t -> t
(** Explanation: the terms were explicitly merged *)

val mk_lit : Lit.t -> t
(** Explanation: we merged [t] and [u] because of literal [t=u],
        or we merged [t] and [true] because of literal [t],
        or [t] and [false] because of literal [¬t] *)

val mk_list : t list -> t
(** Conjunction of explanations *)

val mk_congruence : E_node.t -> E_node.t -> t

val mk_theory :
  Term.t -> Term.t -> (Term.t * Term.t * t list) list -> Proof_term.step_id -> t
(** [mk_theory t u expl_sets pr] builds a theory explanation for
    why [|- t=u]. It depends on sub-explanations [expl_sets] which
    are tuples [ (t_i, u_i, expls_i) ] where [expls_i] are
    explanations that justify [t_i = u_i] in the current congruence closure.

    The proof [pr] is the theory lemma, of the form
    [ (t_i = u_i)_i |- t=u ].
    It is resolved against each [expls_i |- t_i=u_i] obtained from
    [expl_sets], on pivot [t_i=u_i], to obtain a proof of [Gamma |- t=u]
    where [Gamma] is a subset of the literals asserted into the congruence
    closure.

    For example for the lemma [a=b] deduced by injectivity
    from [Some a=Some b] in the theory of datatypes,
    the arguments would be
    [a, b, [Some a, Some b, mk_merge_t (Some a)(Some b)], pr]
    where [pr] is the injectivity lemma [Some a=Some b |- a=b].
*)
