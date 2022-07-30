open Sidekick_core_logic

type step_id = Proof_step.id
type lit = Lit.t

type t = {
  rule_name: string;
  lit_args: lit Iter.t;
  term_args: Term.t Iter.t;
  subst_args: Subst.t Iter.t;
  premises: step_id Iter.t;
}

let pp out _ = Fmt.string out "<proof term>" (* TODO *)

let make ?(lits = Iter.empty) ?(terms = Iter.empty) ?(substs = Iter.empty)
    ?(premises = Iter.empty) rule_name : t =
  {
    rule_name;
    lit_args = lits;
    subst_args = substs;
    term_args = terms;
    premises;
  }
