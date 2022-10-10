open Sidekick_core
module SI = Sidekick_smt_solver.Solver_internal
module MCC = Sidekick_mini_cc

let pp_c out c = Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∨ " Lit.pp) c

let pp_and out c = Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∧ " Lit.pp) c

let add_cc_lit (cc : MCC.t) (lit : Lit.t) : unit =
  let t = Lit.term lit in
  MCC.add_lit cc t (Lit.sign lit)

(* check that this is a proper CC conflict *)
let check_conflict si _cc (confl : Lit.t list) : unit =
  Log.debugf 15 (fun k -> k "(@[check-cc-conflict@ %a@])" pp_c confl);
  let tst = SI.tst si in
  let cc = MCC.create_default tst in
  (* add [¬confl] and check it's unsat *)
  List.iter (fun lit -> add_cc_lit cc @@ Lit.neg lit) confl;
  if MCC.check_sat cc then
    Error.errorf
      "@[<2>check-cc-conflict:@ @[clause %a@]@ is not a UF tautology (negation \
       is sat)@]"
      pp_c confl
  else
    Log.debugf 15 (fun k -> k "(@[check-cc-conflict.ok@ %a@])" pp_c confl)

let check_propagation si _cc p reason : unit =
  let reason = reason () in
  Log.debugf 15 (fun k ->
      k "(@[check-cc-prop@ %a@ :reason %a@])" Lit.pp p pp_and reason);
  let tst = SI.tst si in
  let cc = MCC.create_default tst in
  (* add [reason & ¬lit] and check it's unsat *)
  List.iter (add_cc_lit cc) reason;
  add_cc_lit cc (Lit.neg p);
  if MCC.check_sat cc then
    Error.errorf
      "@[<2>check-cc-prop:@ @[%a => %a@]@ is not a UF tautology (negation is \
       sat)@]"
      pp_and reason Lit.pp p
  else
    Log.debugf 15 (fun k ->
        k "(@[check-cc-prop.ok@ @[%a => %a@]@])" pp_and reason Lit.pp p)

let theory =
  Solver.Smt_solver.Solver.mk_theory ~name:"cc-check"
    ~create_and_setup:(fun ~id:_ si ->
      let n_calls = Stat.mk_int (SI.stats si) "check-cc.call" in
      SI.on_cc_conflict si (fun { cc; th; c } ->
          if not th then (
            Stat.incr n_calls;
            check_conflict si cc c
          )))
    ()
