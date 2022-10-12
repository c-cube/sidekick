open Sidekick_core_logic

type step_id = Step.id
type lit = Lit.t
type local_ref = Step.id

type rule_apply = {
  rule_name: string;
  lit_args: lit list;
  term_args: Term.t list;
  subst_args: Subst.t list;
  premises: step_id list;
  indices: int list;
}

type t =
  | P_ref of step_id
  | P_local of local_ref
  | P_let of (local_ref * t) list * t
  | P_apply of rule_apply

type delayed = unit -> t

let rec pp out = function
  | P_ref r -> Fmt.fprintf out "!%d" r
  | P_local id -> Fmt.fprintf out "s%d" id
  | P_apply r -> Fmt.fprintf out "%s" r.rule_name
  | P_let (bs, bod) ->
    let pp_b out (x, t) = Fmt.fprintf out "s%d := %a" x pp t in
    Fmt.fprintf out "(@[let %a@ in %a@])"
      (Util.pp_list ~sep:"; " pp_b)
      bs pp bod

let local_ref id = P_local id
let ref id = P_ref id
let[@inline] delay f = f

let let_ bs r =
  match bs with
  | [] -> r
  | _ -> P_let (bs, r)

let apply_rule ?(lits = []) ?(terms = []) ?(substs = []) ?(premises = [])
    ?(indices = []) rule_name : t =
  P_apply
    {
      rule_name;
      lit_args = lits;
      subst_args = substs;
      term_args = terms;
      premises;
      indices;
    }
