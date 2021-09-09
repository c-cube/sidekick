

module type ARG = sig
  module Solver : Sidekick_core.SOLVER
  type term = Solver.T.Term.t

  val term_as_eqn : Solver.T.Term.store -> term -> (term*term) option

  val mk_eqn : Solver.T.Term.store -> term -> term -> term
end

module type S = sig
  module Solver : Sidekick_core.SOLVER
  val theory : Solver.theory
end

module Make(A: ARG)
  : S with module Solver = A.Solver
= struct
  module Solver = A.Solver
  module SI = Solver.Solver_internal
  module CC = SI.CC
  module SAT = Solver.Sat_solver
  module Lit = Solver.Lit
  module Term = Solver.T.Term

  let[@inline] is_eqn_ tstore (t:Term.t) : bool =
    match A.term_as_eqn tstore t with
    | Some _ -> true
    | None -> false

  module Instantiation = struct
    type t = {l1: Lit.t; l2: Lit.t; concl: Lit.t}
    let equal a b =
      Lit.equal a.l1 b.l1 &&
      Lit.equal a.l2 b.l2 &&
      Lit.equal a.concl b.concl

    let hash a = CCHash.(combine3 (Lit.hash a.l1) (Lit.hash a.l2) (Lit.hash a.concl))

    let make (tst:Term.store) l1 l2 concl : t =
      assert (Lit.sign l1 && is_eqn_ tst (Lit.term l1));
      assert (Lit.sign l2 && is_eqn_ tst (Lit.term l2));
      assert (Lit.sign concl && is_eqn_ tst (Lit.term concl));
      let l1, l2 =
        if Term.compare (Lit.term l1) (Lit.term l2) < 0
        then l1, l2 else l2, l1 in
      {l1; l2; concl}
  end

  module Inst_tbl = CCHashtbl.Make(Instantiation)

  type t = {
    cc: CC.t;
    sat: SAT.t;
    cpool: SAT.clause_pool_id;
    done_inst: unit Inst_tbl.t;
    stat_cc_confl : int Stat.counter;
  }

  (* TODO: some rate limiting system (a counter that goes up when cc conflict,
     goes down by 5 when a new axiom is instantiated, cannot go below 0?) *)

  let on_conflict (self:t) (cc:CC.t) ~th lits : unit =
    Log.debugf 50 (fun k->k "(@[dyn-trans.confl@ %a@])"
                     (Util.pp_list Lit.pp) lits);
    Stat.incr self.stat_cc_confl;
    (* TODO: find some potential dyn-trans axioms; add them to self.sat
       if they're not in done_inst *)
    ()

  let create_and_setup si sat : unit =
    Log.debugf 1 (fun k->k "(dyn-trans.setup)");
    let self = {
      cc=SI.cc si;
      sat;
      done_inst=Inst_tbl.create 32;
      cpool=SAT.new_clause_pool_gc_fixed_size
          ~descr:"dyn-trans clauses" ~size:200 sat;
      stat_cc_confl=Stat.mk_int (SI.stats si) "dyn-trans-confl";
    } in
    CC.on_conflict self.cc (on_conflict self);
    ()

  let theory =
    Solver.mk_theory
      ~name:"dyn-trans"
      ~create_and_setup ()
end
