
(** {1 Theory for if-then-else} *)

module Ite_view = struct
  type 't t =
    | T_ite of 't * 't * 't
    | T_bool of bool
    | T_other of 't
end

module type ARG = sig
  module S : Sidekick_core.SOLVER
  type term = S.A.Term.t

  val view_as_ite : term -> term Ite_view.t

  module T_set : CCSet.S with type elt = term
end

module type S = sig
  module A : ARG
  val theory : A.S.theory
end

module Make(A : ARG)
(*   : S with module A = A *)
= struct
  module A = A
  module Solver = A.S.Solver_internal
  module N = Solver.N
  module Expl = Solver.Expl
  module T = A.S.A.Term

  type lit = A.S.A.Lit.t
  type term = T.t

  module Data = struct
    type t = A.T_set.t
    (* associate to each class [t] the set of [ite a b c] where [a=t] *)

    let pp = Fmt.(map A.T_set.to_seq @@ seq ~sep:(return ",@ ") T.pp)
    let merge = A.T_set.union
  end

  let k = Solver.Key.create (module Data)

  type t = unit

  let on_merge (solver:Solver.t) n1 n2 e_n1_n2 : unit =
    Log.debugf 5
      (fun k->k "(@[th-ite.on_merge@ :c1 %a@ :c2 %a@])" N.pp n1 N.pp n2); 
    (* check if [n1] has some [ite] parents, and if [n2] is true/false *)
    let check_ n1 n2 =
      match Solver.cc_data solver ~k n1, A.view_as_ite (N.term n2) with
      | Some set, T_bool n2_true ->
        assert (not @@ A.T_set.is_empty set);
        A.T_set.iter
          (fun parent_1 -> match A.view_as_ite parent_1 with
             | T_ite (a1,b1,c1) ->
               let n_parent1 = Solver.cc_add_term solver parent_1 in
               let expl =
                 Expl.mk_list [
                   e_n1_n2;
                   Expl.mk_merge n1 (Solver.cc_add_term solver a1)] in
               if n2_true then (
                 (* [a1 = n1 = n2 = true] so [if a1 b1 c1 = b1] *)
                 Solver.cc_merge solver n_parent1 (Solver.cc_add_term solver b1) expl
               ) else (
                 (* [a1 = n1 = n2 = false] so [if a1 b1 c1 = c1] *)
                 Solver.cc_merge solver n_parent1 (Solver.cc_add_term solver c1) expl
               )
             | _ -> assert false)
          set
      | _ -> ()
    in
    check_ n1 n2;
    check_ n2 n1;
    ()

  let on_new_term (solver:Solver.t) _n (t:T.t) =
    match A.view_as_ite t with
    | T_ite (a,_,_) ->
      (* add [t] to parents of [a] *)
      let n_a = Solver.cc_find solver @@ Solver.cc_add_term solver a in
      Solver.cc_add_data solver n_a ~k (A.T_set.singleton t);
      None
    | _ -> None

  let create_and_setup (solver:Solver.t) : t =
    Solver.on_cc_merge_all solver on_merge;
    Solver.on_cc_new_term solver ~k on_new_term;
    ()

  let theory = A.S.mk_theory ~name:"ite" ~create_and_setup ()
end

