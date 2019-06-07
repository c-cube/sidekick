(** {1 Theory of Booleans} *)

(** {2 Signatures for booleans} *)
module View = struct
  type 'a t =
    | B_not of 'a
    | B_and of 'a IArray.t
    | B_or of 'a IArray.t
    | B_imply of 'a IArray.t * 'a
    | B_atom of 'a
end

module type ARG = sig
  module S : Sidekick_core.SOLVER

  type term = S.A.Term.t

  val view_as_bool : term -> term View.t
  val mk_bool : S.A.Term.state -> term View.t -> term
end

module type S = sig
  module A : ARG
  val theory : A.S.theory
end

(** Theory with dynamic reduction to clauses *)
module Make_dyn_tseitin(A : ARG)
(*   : S with module A = A *)
= struct
  (* TODO (long term): relevancy propagation *)

  (* TODO: Tseitin on the fly when a composite boolean term is asserted.
    --> maybe, cache the clause inside the literal *)

  module A = A
  module SI = A.S.Solver_internal
  module T = SI.A.Term
  module Lit = SI.A.Lit

  type term = T.t

  module T_tbl = CCHashtbl.Make(T)

  type t = {
    expanded: unit T_tbl.t; (* set of literals already expanded *)
  }

  let tseitin ~final (self:t) (solver:SI.t) (lit:Lit.t) (lit_t:term) (v:term View.t) : unit =
    Log.debugf 5 (fun k->k "(@[th_bool.tseitin@ %a@])" Lit.pp lit);
    let expanded () = T_tbl.mem self.expanded lit_t in
    let add_axiom c =
      T_tbl.replace self.expanded lit_t ();
      SI.add_persistent_axiom solver c
    in
    match v with
    | B_not _ -> assert false (* normalized *)
    | B_atom _ -> () (* CC will manage *)
    | B_and subs ->
      if Lit.sign lit then (
        (* propagate [lit => subs_i] *)
        IArray.iter
          (fun sub ->
             let sublit = SI.mk_lit solver sub in
             SI.propagate_l solver sublit [lit])
          subs
      ) else if final && not @@ expanded () then (
        (* axiom [¬lit => ∨_i ¬ subs_i] *)
        let subs = IArray.to_list subs in
        let c = Lit.neg lit :: List.map (SI.mk_lit solver ~sign:false) subs in
        add_axiom c
      )
    | B_or subs ->
      if not @@ Lit.sign lit then (
        (* propagate [¬lit => ¬subs_i] *)
        IArray.iter
          (fun sub ->
             let sublit = SI.mk_lit solver ~sign:false sub in
             SI.add_local_axiom solver [Lit.neg lit; sublit])
          subs
      ) else if final && not @@ expanded () then (
        (* axiom [lit => ∨_i subs_i] *)
        let subs = IArray.to_list subs in
        let c = Lit.neg lit :: List.map (SI.mk_lit solver ~sign:true) subs in
        add_axiom c
      )
    | B_imply (guard,concl) ->
      if Lit.sign lit && final && not @@ expanded () then (
        (* axiom [lit => ∨_i ¬guard_i ∨ concl] *)
        let guard = IArray.to_list guard in
        let c =
          SI.mk_lit solver concl :: Lit.neg lit ::
          List.map (SI.mk_lit solver ~sign:false) guard in
        add_axiom c
      ) else if not @@ Lit.sign lit then (
        (* propagate [¬lit => ¬concl] *)
        SI.propagate_l solver (SI.mk_lit solver ~sign:false concl) [lit];
        (* propagate [¬lit => ∧_i guard_i] *)
        IArray.iter
          (fun sub ->
             let sublit = SI.mk_lit solver ~sign:true sub in
             SI.propagate_l solver sublit [lit])
          guard
      )

  let check_ ~final self solver lits =
    lits
      (fun lit ->
         let t = Lit.term lit in
         match A.view_as_bool t with
         | B_atom _ -> ()
         | v -> tseitin ~final self solver lit t v)

  let partial_check (self:t) acts (lits:Lit.t Iter.t) =
    check_ ~final:false self acts lits

  let final_check (self:t) acts (lits:Lit.t Iter.t) =
    check_ ~final:true self acts lits

  let create_and_setup (solver:SI.t) : t =
    let self = {expanded=T_tbl.create 24} in
    SI.on_final_check solver (final_check self);
    SI.on_partial_check solver (partial_check self);
    self

  let theory =
    A.S.mk_theory ~name:"boolean" ~create_and_setup ()
end
