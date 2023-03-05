module H = CCHash

(** A level expression *)
type level =
  | L_zero
  | L_succ of level
  | L_var of string  (** variable *)
  | L_max of level * level  (** max *)
  | L_imax of level * level  (** impredicative max. *)

type term_view =
  | E_type of level
  | E_bound_var of bvar
  | E_const of const
  | E_app of term * term
  | E_lam of term * term
  | E_pi of term * term

and bvar = { bv_idx: int }
and const = { c_name: string; c_ty: term }

and term = {
  view: term_view;
  mutable flags: int;  (** contains: [highest DB var | 1:has free vars] *)
}
