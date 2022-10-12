open Types_

type t = { lits: Lit.t list; pr: Proof.Pterm.delayed }

let pp out (self : t) =
  Fmt.fprintf out "(@[resolved-expl@ %a@])" (Util.pp_list Lit.pp) self.lits
