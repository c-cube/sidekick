
open Solver_types

type t = Lit.t list

let lits c = c

let pp out c = match lits c with
  | [] -> Fmt.string out "false"
  | [lit] -> Lit.pp out lit
  | l ->
    Format.fprintf out "[@[<hv>%a@]]"
      (Util.pp_list ~sep:" ∨ " Lit.pp) l

(* canonical form: sorted list *)
let make =
  fun l -> CCList.sort_uniq ~cmp:Lit.compare l

let equal_ c1 c2 = CCList.equal Lit.equal (lits c1) (lits c2)
let hash_ c = Hash.list Lit.hash (lits c)

module Tbl = CCHashtbl.Make(struct
    type t_ = t
    type t = t_
    let equal = equal_
    let hash = hash_
  end)

let iter f c = List.iter f (lits c)
let to_seq c = Sequence.of_list (lits c)
