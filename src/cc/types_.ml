include Sidekick_core

type e_node = {
  n_term: Term.t;
  mutable n_sig0: signature option; (* initial signature *)
  mutable n_bits: Bits.t; (* bitfield for various properties *)
  mutable n_parents: e_node Bag.t; (* parent terms of this node *)
  mutable n_root: e_node;
  (* representative of congruence class (itself if a representative) *)
  mutable n_next: e_node; (* pointer to next element of congruence class *)
  mutable n_size: int; (* size of the class *)
  mutable n_as_lit: Lit.t option;
  (* TODO: put into payload? and only in root? *)
  mutable n_expl: explanation_forest_link;
      (* the rooted forest for explanations *)
}
(** A node of the congruence closure.
      An equivalence class is represented by its "root" element,
      the representative. *)

and signature = (Const.t, e_node, e_node list) View.t

and explanation_forest_link =
  | FL_none
  | FL_some of { next: e_node; expl: explanation }

(* atomic explanation in the congruence closure *)
and explanation =
  | E_trivial (* by pure reduction, tautologically equal *)
  | E_lit of Lit.t (* because of this literal *)
  | E_merge of e_node * e_node
  | E_merge_t of Term.t * Term.t
  | E_congruence of e_node * e_node (* caused by normal congruence *)
  | E_and of explanation * explanation
  | E_theory of
      Term.t
      * Term.t
      * (Term.t * Term.t * explanation list) list
      * Proof_term.step_id
