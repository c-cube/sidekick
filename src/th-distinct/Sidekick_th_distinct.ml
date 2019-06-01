
module type ARG = sig
  module S : Sidekick_core.SOLVER
  val as_distinct : S.A.Term.t -> S.A.Term.t Iter.t option
  val mk_eq : S.A.Term.state -> S.A.Term.t -> S.A.Term.t -> S.A.Term.t
end
  
module type S = sig
  module A : ARG
  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module SI = A.S.Solver_internal
  module T = A.S.A.Term
  module Lit = A.S.A.Lit
  module IM = CCMap.Make(Lit)
  module N = SI.N
  module Expl = SI.Expl

  type term = T.t

  module Data = struct
    type t = T.t IM.t (* "distinct" lit -> term appearing under it*)

    let merge m1 m2 =
      IM.merge_safe m1 m2
        ~f:(fun _ pair -> match pair with
            | `Left x | `Right x -> Some x
            | `Both (x,_) -> Some x)

    let pp out m =
      Fmt.fprintf out
        "{@[%a@]}" Fmt.(seq ~sep:(return ",@ ") @@ pair Lit.pp T.pp) (IM.to_seq m)
  end

  (* called when two classes with "distinct" sets are merged *)
  let on_merge (solver:SI.t) n1 m1 n2 m2 expl12 =
    Log.debugf 5
      (fun k->k "(@[th_distinct.on_merge@ @[:n1 %a@ :map2 %a@]@ @[:n2 %a@ :map2 %a@]@])"
          N.pp n1 Data.pp m1 N.pp n2 Data.pp m2);
    let _i: Data.t =
      IM.merge
        (fun lit o1 o2 ->
           match o1, o2 with
           | Some t1, Some t2 ->
             (* conflict! two terms under the same "distinct" [lit]
                are merged, where [lit = distinct(t1,t2,…)].
                The conflict is:
                [lit, t1=n1, t2=n2, expl-merge(n1,n2) ==> false]
             *)
             assert (not @@ T.equal t1 t2);
             let expl = Expl.mk_list
                 [expl12;
                  Expl.mk_lit lit;
                  Expl.mk_merge n1 (SI.cc_add_term solver t1);
                  Expl.mk_merge n2 (SI.cc_add_term solver t2);
                 ] in
             SI.raise_conflict solver expl
           | _ -> None)
        m1 m2
    in ()

  let k = SI.Key.create (module Data)

  module T_tbl = CCHashtbl.Make(T)

  type t = {
    expanded: unit T_tbl.t; (* negative "distinct" that have been case-split on *)
  }

  let pp_c out c = Fmt.fprintf out "(@[<hv>%a@])" (Util.pp_list Lit.pp) c

  (* process one new assertion *)
  let process_lit (self:t) (solver:SI.t) (lit:Lit.t) (lit_t:term) (subs:term Iter.t) : unit =
    Log.debugf 5 (fun k->k "(@[th_distinct.process@ %a@])" Lit.pp lit);
    let add_axiom c = SI.add_persistent_axiom solver c in
    if Lit.sign lit then (
      (* assert [distinct subs], so we update the node of each [t in subs] with [lit] *)
      subs
        (fun sub ->
          let n = SI.cc_add_term solver sub in
          SI.cc_add_data solver n ~k (IM.singleton lit sub));
    ) else if not @@ T_tbl.mem self.expanded lit_t then (
      (* add clause [distinct t1…tn ∨ ∨_{i,j>i} t_i=j] *)
      T_tbl.add self.expanded lit_t ();
      let l = Iter.to_list subs in
      let c =
        Iter.diagonal_l l
        |> Iter.map
          (fun (t,u) -> SI.mk_lit solver @@ A.mk_eq (SI.tst solver) t u)
        |> Iter.to_rev_list
      in
      let c = Lit.neg lit :: c in
      Log.debugf 5 (fun k->k "(@[tseitin.distinct.case-split@ %a@])" pp_c c);
      add_axiom c
    )

  let partial_check st (solver: SI.t) lits : unit =
    lits
      (fun lit ->
         let t = Lit.term lit in
         match A.as_distinct t with
         | None -> ()
         | Some subs -> process_lit st solver lit t subs)

  let create_and_setup (solver:SI.t) : t =
    let self = { expanded=T_tbl.create 8; } in
    SI.on_cc_merge solver ~k on_merge;
    SI.on_final_check solver (partial_check self);
    self

  let theory =
    A.S.mk_theory ~name:"distinct" ~create_and_setup ()
end
