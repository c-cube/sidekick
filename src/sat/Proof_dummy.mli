(** Dummy proof module that does nothing. *)

module Make (Lit : sig
  type t
end) : sig
  include
    Solver_intf.PROOF
      with type lit = Lit.t
       and type t = unit
       and type proof_step = unit
end
