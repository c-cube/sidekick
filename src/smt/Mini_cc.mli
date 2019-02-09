
(** {1 Mini congruence closure} *)

type ('f, 't, 'ts) view = ('f, 't, 'ts) Mini_cc_intf.view =
  | Bool of bool
  | App of 'f * 'ts
  | If of 't * 't * 't

type res = Mini_cc_intf.res =
  | Sat
  | Unsat

module type ARG = Mini_cc_intf.ARG
module type S = Mini_cc_intf.S

module Make(A: ARG)
  : S with type term = A.Term.t
       and type fun_ = A.Fun.t
