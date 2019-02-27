(** {2 Congruence Closure} *)

module type ARG = Congruence_closure_intf.ARG
module type S = Congruence_closure_intf.S

module type THEORY_KEY = Congruence_closure_intf.THEORY_KEY
module Key : THEORY_KEY

module Make(A: ARG)
  : S with type term = A.Term.t
       and type lit = A.Lit.t
       and type fun_ = A.Fun.t
       and type term_state = A.Term.state
       and type proof = A.Proof.t
       and type model = A.Model.t
       and module Key = Key
