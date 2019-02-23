(** {2 Congruence Closure} *)

module type ARG = Congruence_closure_intf.ARG
module type S = Congruence_closure_intf.S
module type THEORY_DATA = Congruence_closure_intf.THEORY_DATA
module type THEORY_KEY = Congruence_closure_intf.THEORY_KEY

type ('t, 'a) theory_data = ('t,'a) Congruence_closure_intf.theory_data

module Key : THEORY_KEY

module Make(A: ARG)
  : S with type term = A.Term.t
       and type lit = A.Lit.t
       and type fun_ = A.Fun.t
       and type term_state = A.Term.state
       and type proof = A.Proof.t
       and type model = A.Model.t
       and module Key = Key
