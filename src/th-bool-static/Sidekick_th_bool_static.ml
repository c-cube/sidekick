(** Theory of boolean formulas.

    This handles formulas containing "and", "or", "=>", "if-then-else", etc.
    *)

(** Boolean-oriented view of terms *)
type ('a, 'args) bool_view =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'args
  | B_or of 'args
  | B_imply of 'args * 'a
  | B_equiv of 'a * 'a
  | B_xor of 'a * 'a
  | B_eq of 'a * 'a
  | B_neq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_opaque_bool of 'a (* do not enter *)
  | B_atom of 'a

(** Argument to the theory *)
module type ARG = sig
  module S : Sidekick_core.SOLVER

  type term = S.T.Term.t

  val view_as_bool : term -> (term, term Iter.t) bool_view
  (** Project the term into the boolean view. *)

  val mk_bool : S.T.Term.store -> (term, term IArray.t) bool_view -> term
  (** Make a term from the given boolean view. *)

  val check_congruence_classes : bool
  (** Configuration: add final-check handler to verify if new boolean formulas
      are present in the congruence closure.
      Only enable if some theories are susceptible to
      create boolean formulas during the proof search. *)

  val lemma_bool_tauto : S.Lit.t Iter.t -> S.P.proof_rule
  (** Boolean tautology lemma (clause) *)

  val lemma_bool_c : string -> term list -> S.P.proof_rule
  (** Basic boolean logic lemma for a clause [|- c].
      [proof_bool_c b name cs] is the rule designated by [name]. *)

  val lemma_bool_equiv : term -> term -> S.P.proof_rule
  (** Boolean tautology lemma (equivalence) *)

  val lemma_ite_true : a:term -> ite:term -> S.P.proof_rule
  (** lemma [a => ite a b c = b] *)

  val lemma_ite_false : a:term -> ite:term -> S.P.proof_rule
  (** lemma [¬a => ite a b c = c] *)

  (** Fresh symbol generator.

      The theory needs to be able to create new terms with fresh names,
      to be used as placeholders for complex formulas during Tseitin
      encoding. *)
  module Gensym : sig
    type t

    val create : S.T.Term.store -> t
    (** New (stateful) generator instance. *)

    val fresh_term : t -> pre:string -> S.T.Ty.t -> term
    (** Make a fresh term of the given type *)
  end
end

(** Signature *)
module type S = sig
  module A : ARG

  type state

  val create : A.S.T.Term.store -> A.S.T.Ty.store -> state

  val simplify : state -> A.S.Solver_internal.simplify_hook
  (** Simplify given term *)

  val cnf : state -> A.S.Solver_internal.preprocess_hook
  (** preprocesses formulas by giving them names and
      adding clauses to equate the name with the boolean formula. *)

  val theory : A.S.theory
  (** A theory that can be added to the solver {!A.S}.

      This theory does most of its work during preprocessing,
      turning boolean formulas into SAT clauses via
      the {{: https://en.wikipedia.org/wiki/Tseytin_transformation}
          Tseitin encoding} . *)
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module Ty = A.S.T.Ty
  module T = A.S.T.Term
  module Lit = A.S.Solver_internal.Lit
  module SI = A.S.Solver_internal

  type state = {
    tst: T.store;
    ty_st: Ty.store;
    gensym: A.Gensym.t;
  }

  let create tst ty_st : state =
    { tst; ty_st;
      gensym=A.Gensym.create tst;
    }

  let[@inline] not_ tst t = A.mk_bool tst (B_not t)
  let[@inline] eq tst a b = A.mk_bool tst (B_eq (a,b))

  let is_true t = match T.as_bool t with Some true -> true | _ -> false
  let is_false t = match T.as_bool t with Some false -> true | _ -> false

  let simplify (self:state) (simp:SI.Simplify.t) (t:T.t) : (T.t * SI.proof_step Iter.t) option =
    let tst = self.tst in
    let steps = ref [] in
    let add_step_ s = steps := s :: !steps in

    let[@inline] ret u =
      Some (u, Iter.of_list !steps)
    in
    (* proof is [t <=> u] *)
    let ret_bequiv t1 u =
      add_step_ @@ A.lemma_bool_equiv t1 u @@ SI.Simplify.proof simp;
      ret u
    in

    match A.view_as_bool t with
    | B_bool _ -> None
    | B_not u when is_true u -> ret_bequiv t (T.bool tst false)
    | B_not u when is_false u -> ret_bequiv t (T.bool tst true)
    | B_not _ -> None
    | B_opaque_bool _ -> None
    | B_and a ->
      if Iter.exists is_false a then ret (T.bool tst false)
      else if Iter.for_all is_true a then ret (T.bool tst true)
      else None
    | B_or a ->
      if Iter.exists is_true a then ret (T.bool tst true)
      else if Iter.for_all is_false a then ret (T.bool tst false)
      else None
    | B_imply (args, u) ->
      if Iter.exists is_false args then ret (T.bool tst true)
      else if is_true u then ret (T.bool tst true)
      else None
    | B_ite (a,b,c) ->
      (* directly simplify [a] so that maybe we never will simplify one
         of the branches *)
      let a, prf_a = SI.Simplify.normalize_t simp a in
      CCOpt.iter add_step_ prf_a;
      begin match A.view_as_bool a with
        | B_bool true ->
          add_step_ @@ A.lemma_ite_true ~a ~ite:t @@ SI.Simplify.proof simp;
          ret b
        | B_bool false ->
          add_step_ @@ A.lemma_ite_false ~a ~ite:t @@ SI.Simplify.proof simp;
          ret c
        | _ ->
          None
      end
    | B_equiv (a,b) when is_true a -> ret_bequiv t b
    | B_equiv (a,b) when is_false a -> ret_bequiv t (not_ tst b)
    | B_equiv (a,b) when is_true b -> ret_bequiv t a
    | B_equiv (a,b) when is_false b -> ret_bequiv t (not_ tst a)
    | B_xor (a,b) when is_false a -> ret_bequiv t b
    | B_xor (a,b) when is_true a -> ret_bequiv t (not_ tst b)
    | B_xor (a,b) when is_false b -> ret_bequiv t a
    | B_xor (a,b) when is_true b -> ret_bequiv t (not_ tst a)
    | B_equiv _ | B_xor _ -> None
    | B_eq (a,b) when T.equal a b -> ret_bequiv t (T.bool tst true)
    | B_neq (a,b) when T.equal a b -> ret_bequiv t (T.bool tst true)
    | B_eq _ | B_neq _ -> None
    | B_atom _ -> None

  let fresh_term self ~for_t ~pre ty =
    let u = A.Gensym.fresh_term self.gensym ~pre ty in
    Log.debugf 20
      (fun k->k "(@[sidekick.bool.proxy@ :t %a@ :for %a@])"
          T.pp u T.pp for_t);
    assert (Ty.equal ty (T.ty u));
    u

  let fresh_lit (self:state) ~for_t ~mk_lit ~pre : T.t * Lit.t =
    let proxy = fresh_term ~for_t ~pre self (Ty.bool self.ty_st) in
    proxy, mk_lit proxy

  let pr_p1_opt p s1 s2 : SI.proof_step =
    CCOpt.map_or ~default:s2 (fun s1 -> SI.P.proof_p1 s1 s2 p) s1

  let pr_p1 p s1 s2 = SI.P.proof_p1 s1 s2 p

  (* preprocess "ite" away *)
  let preproc_ite self si (module PA:SI.PREPROCESS_ACTS) (t:T.t) : (T.t * SI.proof_step Iter.t) option =
    let steps = ref [] in
    let add_step_ s = steps := s :: !steps in

    let ret t = Some (t, Iter.of_list !steps) in

    match A.view_as_bool t with
    | B_ite (a,b,c) ->
      let a', pr_a = SI.simp_t si a in
      CCOpt.iter add_step_ pr_a;
      begin match A.view_as_bool a' with
        | B_bool true ->
          (* [a=true |- ite a b c=b], [|- a=true] ==> [|- t=b] *)
          add_step_ @@ A.lemma_ite_true ~a:a' ~ite:t PA.proof;
          ret b
        | B_bool false ->
          (* [a=false |- ite a b c=c], [|- a=false] ==> [|- t=c] *)
          add_step_ @@ A.lemma_ite_false ~a:a' ~ite:t PA.proof;
          ret c
        | _ ->
          let t_ite = fresh_term self ~for_t:t ~pre:"ite" (T.ty b) in
          SI.define_const si ~const:t_ite ~rhs:t;
          let pr_def = SI.P.define_term t_ite t PA.proof in
          let lit_a = PA.mk_lit_nopreproc a' in
          (* TODO: use unit paramod on each clause with side t=t_ite and on a=a' *)
          PA.add_clause [Lit.neg lit_a; PA.mk_lit_nopreproc (eq self.tst t_ite b)]
            (pr_p1 PA.proof pr_def @@ pr_p1_opt PA.proof pr_a @@
             A.lemma_ite_true ~a:a' ~ite:t PA.proof);
          PA.add_clause [lit_a; PA.mk_lit_nopreproc (eq self.tst t_ite c)]
            (pr_p1 PA.proof pr_def @@ pr_p1_opt PA.proof pr_a @@
             A.lemma_ite_false ~a:a' ~ite:t PA.proof);
          ret t_ite
      end
    | _ -> None

  (* TODO: polarity? *)
  let cnf (self:state) (si:SI.t) (module PA:SI.PREPROCESS_ACTS)
      (t:T.t) : (T.t * _ Iter.t) option =
    Log.debugf 50 (fun k->k"(@[th-bool.cnf@ %a@])" T.pp t);
    let steps = ref [] in
    let[@inline] add_step s = steps := s :: !steps in

    (* handle boolean equality *)
    let equiv_ si ~is_xor ~for_t t_a t_b : Lit.t =
      let a = PA.mk_lit_nopreproc t_a in
      let b = PA.mk_lit_nopreproc t_b in
      let a = if is_xor then Lit.neg a else a in (* [a xor b] is [(¬a) = b] *)
      let t_proxy, proxy = fresh_lit ~for_t ~mk_lit:PA.mk_lit_nopreproc ~pre:"equiv_" self in

      SI.define_const si ~const:t_proxy ~rhs:for_t;
      let pr_def = SI.P.define_term t_proxy for_t PA.proof in
      add_step pr_def;

      let[@inline] add_clause c pr = PA.add_clause c pr in

      (* proxy => a<=> b,
         ¬proxy => a xor b *)
      add_clause [Lit.neg proxy; Lit.neg a; b]
        (pr_p1 PA.proof pr_def @@
         if is_xor then A.lemma_bool_c "xor-e+" [for_t] PA.proof
         else A.lemma_bool_c "eq-e" [for_t; t_a] PA.proof);
      add_clause [Lit.neg proxy; Lit.neg b; a]
        (pr_p1 PA.proof pr_def @@
         if is_xor then A.lemma_bool_c "xor-e-" [for_t] PA.proof
         else A.lemma_bool_c "eq-e" [for_t; t_b] PA.proof);
      add_clause [proxy; a; b]
        (pr_p1 PA.proof pr_def @@
         if is_xor then A.lemma_bool_c "xor-i" [for_t; t_a] PA.proof
         else A.lemma_bool_c "eq-i+" [for_t] PA.proof);
      add_clause [proxy; Lit.neg a; Lit.neg b]
        (pr_p1 PA.proof pr_def @@
         if is_xor then A.lemma_bool_c "xor-i" [for_t; t_b] PA.proof
         else A.lemma_bool_c "eq-i-" [for_t] PA.proof);
      proxy
    in

    (* make a literal for [t], with a proof of [|- abs(t) = abs(lit)] *)
    let rec get_lit_for_term_ t : Lit.t option =
      match A.view_as_bool t with
      | B_opaque_bool _ -> None
      | B_bool _ -> None
      | B_not u ->
        let lit = get_lit_for_term_ u in
        CCOpt.map Lit.neg lit

      | B_and l ->
        let t_subs = Iter.to_list l in
        let subs = List.map PA.mk_lit_nopreproc t_subs in
        let t_proxy, proxy = fresh_lit ~for_t:t ~mk_lit:PA.mk_lit_nopreproc ~pre:"and_" self in
        SI.define_const si ~const:t_proxy ~rhs:t;
        let pr_def = SI.P.define_term t_proxy t PA.proof in
        add_step pr_def;

        (* add clauses *)
        List.iter2
          (fun t_u u ->
             PA.add_clause
               [Lit.neg proxy; u]
               (pr_p1 PA.proof pr_def @@ A.lemma_bool_c "and-e" [t; t_u] PA.proof))
          t_subs subs;
        PA.add_clause (proxy :: List.map Lit.neg subs)
          (pr_p1 PA.proof pr_def @@ A.lemma_bool_c "and-i" [t] PA.proof);
        Some proxy

      | B_or l ->
        let t_subs = Iter.to_list l in
        let subs = List.map PA.mk_lit_nopreproc t_subs in
        let t_proxy, proxy = fresh_lit ~for_t:t ~mk_lit:PA.mk_lit_nopreproc ~pre:"or_" self in
        SI.define_const si ~const:t_proxy ~rhs:t;
        let pr_def = SI.P.define_term t_proxy t PA.proof in
        add_step pr_def;

        (* add clauses *)
        List.iter2
          (fun t_u u ->
             PA.add_clause [Lit.neg u; proxy]
               (pr_p1 PA.proof pr_def @@
                A.lemma_bool_c "or-i" [t; t_u] PA.proof))
          t_subs subs;
        PA.add_clause (Lit.neg proxy :: subs)
          (pr_p1 PA.proof pr_def @@ A.lemma_bool_c "or-e" [t] PA.proof);
        Some proxy

      | B_imply (t_args, t_u) ->
        (* transform into [¬args \/ u] on the fly *)
        let t_args = Iter.to_list t_args in
        let args = List.map (fun t -> Lit.neg (PA.mk_lit_nopreproc t)) t_args in
        let u = PA.mk_lit_nopreproc t_u in
        let subs = u :: args in

        (* now the or-encoding *)
        let t_proxy, proxy =
          fresh_lit ~for_t:t ~mk_lit:PA.mk_lit_nopreproc ~pre:"implies_" self in
        SI.define_const si ~const:t_proxy ~rhs:t;
        let pr_def = SI.P.define_term t_proxy t PA.proof in
        add_step pr_def;

        (* add clauses *)
        List.iter2
          (fun t_u u ->
             PA.add_clause [Lit.neg u; proxy]
               (pr_p1 PA.proof pr_def @@
                A.lemma_bool_c "imp-i" [t_proxy; t_u] PA.proof))
          (t_u::t_args) subs;
        PA.add_clause (Lit.neg proxy :: subs)
          (pr_p1 PA.proof pr_def @@
           A.lemma_bool_c "imp-e" [t_proxy] PA.proof);
        Some proxy

      | B_ite _ | B_eq _ | B_neq _ -> None
      | B_equiv (a,b) -> Some (equiv_ si ~for_t:t ~is_xor:false a b)
      | B_xor  (a,b) -> Some (equiv_ si ~for_t:t ~is_xor:true a b)
      | B_atom _ -> None
    in

    begin match get_lit_for_term_ t with
      | None -> None
      | Some lit ->
        let u = Lit.term lit in
        (* put sign back as a "not" *)
        let u = if Lit.sign lit then u else A.mk_bool self.tst (B_not u) in
        if T.equal u t then None else Some (u, Iter.of_list !steps)
    end

  (* check if new terms were added to the congruence closure, that can be turned
     into clauses *)
  let check_new_terms (self:state) si (acts:SI.theory_actions) (_trail:_ Iter.t) : unit =
    let cc_ = SI.cc si in
    let all_terms =
      let open SI in
      CC.all_classes cc_
      |> Iter.flat_map CC.N.iter_class
      |> Iter.map CC.N.term
    in
    let cnf_of t =
      let pacts = SI.preprocess_acts_of_acts si acts in
      cnf self si pacts t
    in
    begin
      all_terms
        (fun t -> match cnf_of t with
           | None -> ()
           | Some u ->
             Log.debugf 5
               (fun k->k "(@[th-bool-static.final-check.cnf@ %a@ :yields %a@])"
                   T.pp t T.pp u);
             SI.CC.merge_t cc_ t u (SI.CC.Expl.mk_list []);
             ());
    end;
    ()

  let create_and_setup si =
    Log.debug 2 "(th-bool.setup)";
    let st = create (SI.tst si) (SI.ty_st si) in
    SI.add_simplifier si (simplify st);
    SI.on_preprocess si (preproc_ite st);
    SI.on_preprocess si (cnf st);
    if A.check_congruence_classes then (
      Log.debug 5 "(th-bool.add-final-check)";
      SI.on_final_check si (check_new_terms st);
    );
    st

  let theory =
    A.S.mk_theory
      ~name:"th-bool"
      ~create_and_setup
      ()
end
