
(* TODO (long term): relevancy propagation *)

(* TODO: Tseitin on the fly when a composite boolean term is asserted.
  --> maybe, cache the clause inside the literal *)

module Theory = Sidekick_smt.Theory
open Bool_intf

module type ARG = Bool_intf.BOOL_TERM
  with type t = Sidekick_smt.Term.t
   and type state = Sidekick_smt.Term.state

module Make(Term : ARG) = struct
  type term = Term.t

  module T_tbl = CCHashtbl.Make(Term)

  module Lit = struct
    include Sidekick_smt.Lit
    let eq tst a b = atom tst ~sign:true @@ Term.make tst (B_eq (a,b))
    let neq tst a b = neg @@ eq tst a b
  end

  let pp_c out c = Fmt.fprintf out "(@[<hv>%a@])" (Util.pp_list Lit.pp) c

  type t = {
    tst: Term.state;
    expanded: unit T_tbl.t; (* set of literals already expanded *)
  }

  let tseitin ~final (self:t) (acts:Theory.actions) (lit:Lit.t) (lit_t:term) (v:term view) : unit =
    let (module A) = acts in
    Log.debugf 5 (fun k->k "(@[th_bool.tseitin@ %a@])" Lit.pp lit);
    let expanded () = T_tbl.mem self.expanded lit_t in
    let add_axiom c =
      T_tbl.replace self.expanded lit_t ();
      A.add_persistent_axiom c
    in
    match v with
    | B_not _ -> assert false (* normalized *)
    | B_atom _ | B_eq _ -> () (* CC will manage *)
    | B_distinct l ->
      let l = IArray.to_list l in
      if Lit.sign lit then (
        A.propagate_distinct l ~neq:lit_t lit
      ) else if final && not @@ expanded () then (
        (* add clause [distinct t1…tn ∨ ∨_{i,j>i} t_i=j] *)
        let c =
          Sequence.diagonal_l l
          |> Sequence.map (fun (t,u) -> Lit.eq self.tst t u)
          |> Sequence.to_rev_list
        in
        let c = Lit.neg lit :: c in
        Log.debugf 5 (fun k->k "(@[tseitin.distinct.case-split@ %a@])" pp_c c);
        add_axiom c
      )
    | B_and subs ->
      if Lit.sign lit then (
        (* propagate [lit => subs_i] *)
        IArray.iter
          (fun sub ->
             let sublit = Lit.atom self.tst sub in
             A.propagate_l sublit [lit])
          subs
      ) else if final && not @@ expanded () then (
        (* axiom [¬lit => ∨_i ¬ subs_i] *)
        let subs = IArray.to_list subs in
        let c = Lit.neg lit :: List.map (Lit.atom self.tst ~sign:false) subs in
        add_axiom c
      )
    | B_or subs ->
      if not @@ Lit.sign lit then (
        (* propagate [¬lit => ¬subs_i] *)
        IArray.iter
          (fun sub ->
             let sublit = Lit.atom self.tst ~sign:false sub in
             A.add_local_axiom [Lit.neg lit; sublit])
          subs
      ) else if final && not @@ expanded () then (
        (* axiom [lit => ∨_i subs_i] *)
        let subs = IArray.to_list subs in
        let c = Lit.neg lit :: List.map (Lit.atom self.tst ~sign:true) subs in
        add_axiom c
      )
    | B_imply (guard,concl) ->
      if Lit.sign lit && final && not @@ expanded () then (
        (* axiom [lit => ∨_i ¬guard_i ∨ concl] *)
        let guard = IArray.to_list guard in
        let c = Lit.atom self.tst concl :: Lit.neg lit :: List.map (Lit.atom self.tst ~sign:false) guard in
        add_axiom c
      ) else if not @@ Lit.sign lit then (
        (* propagate [¬lit => ¬concl] *)
        A.propagate_l (Lit.atom self.tst ~sign:false concl) [lit];
        (* propagate [¬lit => ∧_i guard_i] *)
        IArray.iter
          (fun sub ->
             let sublit = Lit.atom self.tst ~sign:true sub in
             A.propagate_l sublit [lit])
          guard
      )

  let check_ ~final self acts lits =
    lits
      (fun lit ->
         let t = Lit.term lit in
         match Term.view_as_bool t with
         | B_atom _ | B_eq _ -> ()
         | v -> tseitin ~final self acts lit t v)

  let partial_check (self:t) acts (lits:Lit.t Sequence.t) =
    check_ ~final:false self acts lits

  let final_check (self:t) acts (lits:Lit.t Sequence.t) =
    check_ ~final:true self acts lits

  let th =
    Theory.make
      ~partial_check
      ~final_check
      ~name:"boolean"
      ~create:(fun tst -> {tst; expanded=T_tbl.create 24})
      ?mk_model:None (* entirely interpreted *)
      ()

end
