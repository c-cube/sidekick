
type ('f, 't, 'ts) view = ('f, 't, 'ts) Congruence_closure_intf.view =
  | Bool of bool
  | App_fun of 'f * 'ts
  | App_ho of 't * 'ts
  | If of 't * 't * 't
  | Eq of 't * 't
  | Not of 't
  | Opaque of 't (* do not enter *)

(** Parameter for the congruence closure *)
module type TERM_LIT = Congruence_closure_intf.TERM_LIT
module type ARG = Congruence_closure_intf.ARG
module type S = Congruence_closure.S

module Mini_cc = Mini_cc
module Congruence_closure = Congruence_closure
module Make = Congruence_closure.Make

