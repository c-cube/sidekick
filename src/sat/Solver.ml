(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

module type S = Solver_intf.S

open Solver_intf

module Make (Th : Theory_intf.S) = struct
  module S = Internal.Make(Th)

  module Proof = S.Proof

  exception UndecidedLit = S.UndecidedLit

  type formula = S.formula
  type atom = S.atom
  type clause = S.clause
  type theory = Th.t
  type proof = S.proof
  type lemma = S.lemma
  type premise = S.premise =
    | Hyp
    | Lemma of lemma
    | Simplified of clause
    | History of clause list

  type t = S.t
  type solver = t

  let[@inline] create ?size () : t = S.create ?size ()

  (* Result type *)
  type res =
    | Sat of formula sat_state
    | Unsat of (clause,proof) unsat_state

  let pp_all st lvl status =
    Log.debugf lvl
      (fun k -> k
          "@[<v>%s - Full resume:@,@[<hov 2>Trail:@\n%a@]@,\
           @[<hov 2>Clauses:@\n%a@]@]@."
          status
          (Vec.print ~sep:"" S.Atom.debug) (S.trail st)
          (Vec.print ~sep:"" S.Clause.debug) st.S.clauses
      )

  let mk_sat (st:S.t) : _ sat_state =
    pp_all st 99 "SAT";
    let iter f : unit = Vec.iter (fun a -> f a.S.lit) (S.trail st) in
    Sat_state {
      eval = S.eval st;
      eval_level = S.eval_level st;
      iter_trail = iter;
    }

  let mk_unsat (st:S.t) : (_,_) unsat_state =
    pp_all st 99 "UNSAT";
    let unsat_conflict () =
      match S.unsat_conflict st with
      | None -> assert false
      | Some c -> c
    in
    let get_proof () = unsat_conflict () in
    Unsat_state { unsat_conflict; get_proof; }

  let theory = S.theory

  (* Wrappers around internal functions*)
  let[@inline] assume ?(permanent=true) st ?tag cls : unit =
    S.assume ~permanent st ?tag cls

  let[@inline] add_clause ~permanent st c : unit =
    S.add_clause_user ~permanent st c

  let solve (st:t) ?(assumptions=[]) () =
    try
      S.solve ~assumptions st;
      Sat (mk_sat st)
    with S.Unsat ->
      Unsat (mk_unsat st)

  let n_vars = S.n_vars
  let unsat_core = S.Proof.unsat_core

  let true_at_level0 st a =
    try
      let b, lev = S.eval_level st a in
      b && lev = 0
    with S.UndecidedLit -> false

  let[@inline] get_tag cl = S.(cl.tag)

  let actions = S.actions

  let export (st:t) : S.clause export =
    let clauses = st.S.clauses in
    {clauses}

  let check_model = S.check_model

  module Atom = S.Atom

  module Clause = struct
    include S.Clause

    let forms c = atoms c |> IArray.of_array_map Atom.get_formula
    let forms_l c = atoms_l c |> List.map Atom.get_formula

    let[@inline] make ?tag (a:atom array) : t = S.Clause.make ?tag a S.Hyp
    let[@inline] make_l ?tag l : t = S.Clause.make_l ?tag l S.Hyp

    let of_formulas st ?tag l =
      let l = List.map (Atom.make st) l in
      make_l ?tag l
  end

  module Formula = S.Formula
end
