(** Formulas (boolean terms).

    This module defines function symbols, constants, and views
    to manipulate boolean formulas in {!Sidekick_base}.
    This is useful to have the ability to use boolean connectives instead
    of being limited to clauses; by using {!Sidekick_th_bool_static},
    the formulas are turned into clauses automatically for you.
*)

open Types_

type term = Term.t

type 'a view = 'a Sidekick_core.Bool_view.t =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'a list
  | B_or of 'a list
  | B_imply of 'a * 'a
  | B_equiv of 'a * 'a
  | B_xor of 'a * 'a
  | B_eq of 'a * 'a
  | B_neq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_atom of 'a

val view : term -> term view
val bool : Term.store -> bool -> term
val not_ : Term.store -> term -> term
val and_ : Term.store -> term -> term -> term
val or_ : Term.store -> term -> term -> term
val eq : Term.store -> term -> term -> term
val neq : Term.store -> term -> term -> term
val imply : Term.store -> term -> term -> term
val equiv : Term.store -> term -> term -> term
val xor : Term.store -> term -> term -> term
val ite : Term.store -> term -> term -> term -> term
val distinct_l : Term.store -> term list -> term
val const_decoders : Const.decoders

(* *)

val and_l : Term.store -> term list -> term
val or_l : Term.store -> term list -> term
val imply_l : Term.store -> term list -> term -> term
val mk_of_view : Term.store -> term view -> term

(* TODO?
   val make : Term.store -> (term, term list) view -> term
*)
