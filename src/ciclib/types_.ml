module H = CCHash

type binder = BD | BI | BS | BC

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
  | E_const of const * level list  (** constant instantiated with universes *)
  | E_app of term * term
  | E_lam of binder * string * term * term
  | E_pi of binder * string * term * term

and bvar = { bv_idx: int } [@@unboxed]
and const = { c_name: string } [@@unboxed]

and term = {
  view: term_view;
  mutable flags: int;  (** contains: [highest DB var | 1:has free vars] *)
}

type cstor = { c_name: string; c_ty: term }

type spec = {
  name: string;
  univ_params: string list;
  n_params: int;
  ty: term;
  cstors: cstor list;
}
(** Inductive spec *)
