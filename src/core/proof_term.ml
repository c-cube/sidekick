open Sidekick_core_logic

type step_id = Proof_step.id
type local_ref = int
type lit = Lit.t

type rule_apply = {
  rule_name: string;
  lit_args: lit list;
  term_args: Term.t list;
  subst_args: Subst.t list;
  premises: step_id list;
}

type t =
  | P_ref of step_id
  | P_local of local_ref
  | P_let of (local_ref * t) list * t
  | P_apply of rule_apply

type delayed = unit -> t

let pp out _ = Fmt.string out "<proof term>" (* TODO *)

let local_ref id = P_local id
let ref_ id = P_ref id

let let_ bs r =
  match bs with
  | [] -> r
  | _ -> P_let (bs, r)

let apply_rule ?(lits = []) ?(terms = []) ?(substs = []) ?(premises = [])
    rule_name : t =
  P_apply
    {
      rule_name;
      lit_args = lits;
      subst_args = substs;
      term_args = terms;
      premises;
    }
