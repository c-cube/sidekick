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

module type PROOF = sig
  type proof
  type proof_step
  type term
  type lit

  val lemma_bool_tauto : lit Iter.t -> proof -> proof_step
  (** Boolean tautology lemma (clause) *)

  val lemma_bool_c : string -> term list -> proof -> proof_step
  (** Basic boolean logic lemma for a clause [|- c].
      [proof_bool_c b name cs] is the rule designated by [name]. *)

  val lemma_bool_equiv : term -> term -> proof -> proof_step
  (** Boolean tautology lemma (equivalence) *)

  val lemma_ite_true : ite:term -> proof -> proof_step
  (** lemma [a ==> ite a b c = b] *)

  val lemma_ite_false : ite:term -> proof -> proof_step
  (** lemma [¬a ==> ite a b c = c] *)
end

(** Argument to the theory *)
module type ARG = sig
  module S : Sidekick_core.SOLVER

  type term = S.T.Term.t

  val view_as_bool : term -> (term, term Iter.t) bool_view
  (** Project the term into the boolean view. *)

  val mk_bool : S.T.Term.store -> (term, term IArray.t) bool_view -> term
  (** Make a term from the given boolean view. *)

  include PROOF
    with type proof := S.P.t
     and type proof_step := S.P.proof_step
     and type lit := S.Lit.t
     and type term := S.T.Term.t

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

    let proof = SI.Simplify.proof simp in
    let steps = ref [] in
    let add_step_ s = steps := s :: !steps in

    let add_step_eq a b ~using ~c0 :unit =
      add_step_ @@ SI.P.lemma_rw_clause c0 (SI.Simplify.proof simp)
        ~using
        ~res:(Iter.return (Lit.atom tst (A.mk_bool tst (B_eq (a,b)))))
    in

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
      Option.iter add_step_ prf_a;
      begin match A.view_as_bool a with
        | B_bool true ->
          add_step_eq t b ~using:(Iter.of_opt prf_a)
            ~c0:(A.lemma_ite_true ~ite:t proof);
          ret b

        | B_bool false ->
          add_step_eq t c ~using:(Iter.of_opt prf_a)
            ~c0:(A.lemma_ite_false ~ite:t proof);
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

  (* TODO: polarity? *)
  let cnf (self:state) (si:SI.t)
      (module PA:SI.PREPROCESS_ACTS) (t:T.t) : unit =
    Log.debugf 50 (fun k->k"(@[th-bool.cnf@ %a@])" T.pp t);

    (* handle boolean equality *)
    let equiv_ _si ~is_xor ~t t_a t_b : unit =
      let a = PA.mk_lit t_a in
      let b = PA.mk_lit t_b in
      let a = if is_xor then Lit.neg a else a in (* [a xor b] is [(¬a) = b] *)
      let lit = PA.mk_lit t in

      (* proxy => a<=> b,
         ¬proxy => a xor b *)
      PA.add_clause [Lit.neg lit; Lit.neg a; b]
        (if is_xor then A.lemma_bool_c "xor-e+" [t] PA.proof
         else A.lemma_bool_c "eq-e" [t; t_a] PA.proof);
      PA.add_clause [Lit.neg lit; Lit.neg b; a]
        (if is_xor then A.lemma_bool_c "xor-e-" [t] PA.proof
         else A.lemma_bool_c "eq-e" [t; t_b] PA.proof);
      PA.add_clause [lit; a; b]
        (if is_xor then A.lemma_bool_c "xor-i" [t; t_a] PA.proof
         else A.lemma_bool_c "eq-i+" [t] PA.proof);
      PA.add_clause [lit; Lit.neg a; Lit.neg b]
        (if is_xor then A.lemma_bool_c "xor-i" [t; t_b] PA.proof
         else A.lemma_bool_c "eq-i-" [t] PA.proof);
    in

    (* make a literal for [t], with a proof of [|- abs(t) = abs(lit)] *)
    begin match A.view_as_bool t with
      | B_opaque_bool _ -> ()
      | B_bool _ -> ()
      | B_not _ -> ()

      | B_and l ->
        let t_subs = Iter.to_list l in
        let lit = PA.mk_lit t in
        let subs = List.map PA.mk_lit t_subs in

        (* add clauses *)
        List.iter2
          (fun t_u u ->
             PA.add_clause
               [Lit.neg lit; u]
               (A.lemma_bool_c "and-e" [t; t_u] PA.proof))
          t_subs subs;
        PA.add_clause (lit :: List.map Lit.neg subs)
          (A.lemma_bool_c "and-i" [t] PA.proof);

      | B_or l ->
        let t_subs = Iter.to_list l in
        let subs = List.map PA.mk_lit t_subs in
        let lit = PA.mk_lit t in

        (* add clauses *)
        List.iter2
          (fun t_u u ->
             PA.add_clause [Lit.neg u; lit]
               (A.lemma_bool_c "or-i" [t; t_u] PA.proof))
          t_subs subs;
        PA.add_clause (Lit.neg lit :: subs)
          (A.lemma_bool_c "or-e" [t] PA.proof);

      | B_imply (t_args, t_u) ->
        (* transform into [¬args \/ u] on the fly *)
        let t_args = Iter.to_list t_args in
        let args = List.map (fun t -> Lit.neg (PA.mk_lit t)) t_args in
        let u = PA.mk_lit t_u in
        let subs = u :: args in

        (* now the or-encoding *)
        let lit = PA.mk_lit t in

        (* add clauses *)
        List.iter2
          (fun t_u u ->
             PA.add_clause [Lit.neg u; lit]
               (A.lemma_bool_c "imp-i" [t; t_u] PA.proof))
          (t_u::t_args) subs;
        PA.add_clause (Lit.neg lit :: subs)
          (A.lemma_bool_c "imp-e" [t] PA.proof);

      | B_ite (a,b,c) ->
        let lit_a = PA.mk_lit a in
        PA.add_clause [Lit.neg lit_a; PA.mk_lit (eq self.tst t b)]
          (A.lemma_ite_true ~ite:t PA.proof);
        PA.add_clause [lit_a; PA.mk_lit (eq self.tst t c)]
          (A.lemma_ite_false ~ite:t PA.proof);

      | B_eq _ | B_neq _ -> ()
      | B_equiv (a,b) -> equiv_ si ~t ~is_xor:false a b
      | B_xor  (a,b) -> equiv_ si ~t ~is_xor:true a b
      | B_atom _ -> ()
    end;
    ()

  let create_and_setup si =
    Log.debug 2 "(th-bool.setup)";
    let st = create (SI.tst si) (SI.ty_st si) in
    SI.add_simplifier si (simplify st);
    SI.on_preprocess si (cnf st);
    st

  let theory =
    A.S.mk_theory
      ~name:"th-bool"
      ~create_and_setup
      ()
end
