open Types_

type t = { lits: Lit.t list; pr: Proof_trace.t -> Proof_term.step_id }

let pp out (self : t) =
  Fmt.fprintf out "(@[resolved-expl@ %a@])" (Util.pp_list Lit.pp) self.lits
