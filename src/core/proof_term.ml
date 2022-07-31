open Sidekick_core_logic

type step_id = Proof_step.id
type lit = Lit.t

type data = {
  rule_name: string;
  lit_args: lit list;
  term_args: Term.t list;
  subst_args: Subst.t list;
  premises: step_id list;
}

type t = unit -> data

let pp out _ = Fmt.string out "<proof term>" (* TODO *)

let make_data ?(lits = []) ?(terms = []) ?(substs = []) ?(premises = [])
    rule_name : data =
  {
    rule_name;
    lit_args = lits;
    subst_args = substs;
    term_args = terms;
    premises;
  }
