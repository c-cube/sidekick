(** {2 Congruence Closure} *)

module type ARG = Sidekick_core.CC_ARG
module type S = Sidekick_core.CC_S

module Make(CC_A: ARG)
  : S with module A=CC_A.A and module CC_A = CC_A
