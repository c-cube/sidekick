(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

module type S = Solver_intf.S

open Solver_intf

module Make
    (St : Solver_types.S)
    (Th :  Theory_intf.S with type formula = St.formula
                         and type proof = St.proof)
= struct

  module St = St

  module S = Internal.Make(St)(Th)

  module Proof = S.Proof

  exception UndecidedLit = S.UndecidedLit

  type formula = St.formula
  type atom = St.formula
  type clause = St.clause
  type theory = Th.t

  type t = S.t
  type solver = t

  let[@inline] create ?size th : t = S.create ?size th

  (* Result type *)
  type res =
    | Sat of St.formula sat_state
    | Unsat of (St.clause,Proof.proof) unsat_state

  let pp_all st lvl status =
    Log.debugf lvl
      (fun k -> k
          "@[<v>%s - Full resume:@,@[<hov 2>Trail:@\n%a@]@,\
           @[<hov 2>Temp:@\n%a@]@,@[<hov 2>Hyps:@\n%a@]@,@[<hov 2>Lemmas:@\n%a@]@,@]@."
          status
          (Vec.print ~sep:"" St.Atom.debug) (S.trail st)
          (Vec.print ~sep:"" St.Clause.debug) (S.temp st)
          (Vec.print ~sep:"" St.Clause.debug) (S.hyps st)
          (Vec.print ~sep:"" St.Clause.debug) (S.history st)
      )

  let mk_sat (st:S.t) : _ sat_state =
    pp_all st 99 "SAT";
    let iter f : unit = Vec.iter (fun a -> f a.St.lit) (S.trail st) in
    {
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
    let get_proof () =
      let c = unsat_conflict () in
      S.Proof.prove_unsat c
    in
    { unsat_conflict; get_proof; }

  (* clean local state *)
  let[@inline] cleanup_ (st:t) : unit =
    if st.S.dirty then (
      S.pop st; (* reset *)
      st.S.dirty <- false;
    )

  let theory = S.theory

  (* Wrappers around internal functions*)
  let[@inline] assume st ?tag cls : unit =
    cleanup_ st;
    S.assume st ?tag cls

  let[@inline] add_clause st c : unit =
    cleanup_ st;
    S.add_clause st c

  let solve (st:t) ?(assumptions=[]) () =
    cleanup_ st;
    try
      S.push st;
      st.S.dirty <- true; (* to call [pop] before any other action *)
      S.local st assumptions;
      S.solve st;
      Sat (mk_sat st)
    with S.Unsat ->
      Unsat (mk_unsat st)

  let[@inline] push st =
    cleanup_ st;
    S.push st

  let[@inline] pop st =
    cleanup_ st;
    S.pop st

  let unsat_core = S.Proof.unsat_core

  let true_at_level0 st a =
    try
      let b, lev = S.eval_level st a in
      b && lev = 0
    with S.UndecidedLit -> false

  let get_tag cl = St.(cl.tag)

  let[@inline] new_atom st a =
    cleanup_ st;
    S.new_atom st a

  let export (st:t) : St.clause export =
    let hyps = S.hyps st in
    let history = S.history st in
    let local = S.temp st in
    {hyps; history; local}

  module Clause = struct
    include St.Clause

    let atoms c = St.Clause.atoms c |> Array.map (fun a -> a.St.lit)
    let atoms_l c = St.Clause.atoms_l c |> List.map (fun a -> a.St.lit)

    let make st ?tag l =
      let l = List.map (S.mk_atom st) l in
      St.Clause.make ?tag l St.Hyp
  end

  module Formula = St.Formula
end
