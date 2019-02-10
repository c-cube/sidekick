
type ('f, 't, 'ts) view = ('f, 't, 'ts) CC_types.view =
  | Bool of bool
  | App_fun of 'f * 'ts
  | App_ho of 't * 'ts
  | If of 't * 't * 't
  | Eq of 't * 't
  | Opaque of 't (* do not enter *)

type payload = Congruence_closure.payload = ..

module CC_types = CC_types

(** Parameter for the congruence closure *)
module type TERM_LIT = CC_types.TERM_LIT
module type FULL = CC_types.FULL
module type S = Congruence_closure.S

module Mini_cc = Mini_cc
module Congruence_closure = Congruence_closure

module Make = Congruence_closure.Make

