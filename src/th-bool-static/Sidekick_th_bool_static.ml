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

  val mk_bool : S.T.Term.state -> (term, term IArray.t) bool_view -> term
  (** Make a term from the given boolean view. *)

  val check_congruence_classes : bool
  (** Configuration: add final-check handler to verify if new boolean formulas
      are present in the congruence closure.
      Only enable if some theories are susceptible to
      create boolean formulas during the proof search. *)

  (** Fresh symbol generator.

      The theory needs to be able to create new terms with fresh names,
      to be used as placeholders for complex formulas during Tseitin
      encoding. *)
  module Gensym : sig
    type t

    val create : S.T.Term.state -> t
    (** New (stateful) generator instance. *)

    val fresh_term : t -> pre:string -> S.T.Ty.t -> term
    (** Make a fresh term of the given type *)
  end
end

(** Signature *)
module type S = sig
  module A : ARG

  type state

  val create : A.S.T.Term.state -> A.S.T.Ty.state -> state

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
    tst: T.state;
    ty_st: Ty.state;
    simps: T.t T.Tbl.t; (* cache *)
    cnf: Lit.t T.Tbl.t; (* tseitin CNF *)
    gensym: A.Gensym.t;
  }

  let create tst ty_st : state =
    { tst; ty_st; simps=T.Tbl.create 128;
      cnf=T.Tbl.create 128;
      gensym=A.Gensym.create tst;
    }

  let[@inline] not_ tst t = A.mk_bool tst (B_not t)
  let[@inline] and_a tst a = A.mk_bool tst (B_and a)
  let[@inline] or_a tst a = A.mk_bool tst (B_or a)
  let[@inline] ite tst a b c = A.mk_bool tst (B_ite (a,b,c))
  let[@inline] equiv tst a b = A.mk_bool tst (B_equiv (a,b))
  let[@inline] eq tst a b = A.mk_bool tst (B_eq (a,b))

  let is_true t = match T.as_bool t with Some true -> true | _ -> false
  let is_false t = match T.as_bool t with Some false -> true | _ -> false

  let simplify (self:state) (simp:SI.Simplify.t) (t:T.t) : T.t option =
    let tst = self.tst in
    match A.view_as_bool t with
    | B_bool _ -> None
    | B_not u when is_true u -> Some (T.bool tst false)
    | B_not u when is_false u -> Some (T.bool tst true)
    | B_not _ -> None
    | B_opaque_bool _ -> None
    | B_and a ->
      if Iter.exists is_false a then Some (T.bool tst false)
      else if Iter.for_all is_true a then Some (T.bool tst true)
      else None
    | B_or a ->
      if Iter.exists is_true a then Some (T.bool tst true)
      else if Iter.for_all is_false a then Some (T.bool tst false)
      else None
    | B_imply (args, u) ->
      if Iter.exists is_false args then Some (T.bool tst true)
      else if is_true u then Some (T.bool tst true)
      else None
    | B_ite (a,b,c) ->
      (* directly simplify [a] so that maybe we never will simplify one
         of the branches *)
      let a = SI.Simplify.normalize simp a in
      begin match A.view_as_bool a with
        | B_bool true -> Some b
        | B_bool false -> Some c
        | _ ->
          None
      end
    | B_equiv (a,b) when is_true a -> Some b
    | B_equiv (a,b) when is_false a -> Some (not_ tst b)
    | B_equiv (a,b) when is_true b -> Some a
    | B_equiv (a,b) when is_false b -> Some (not_ tst a)
    | B_xor (a,b) when is_false a -> Some b
    | B_xor (a,b) when is_true a -> Some (not_ tst b)
    | B_xor (a,b) when is_false b -> Some a
    | B_xor (a,b) when is_true b -> Some (not_ tst a)
    | B_equiv _ | B_xor _ -> None
    | B_eq (a,b) when T.equal a b -> Some (T.bool tst true)
    | B_neq (a,b) when T.equal a b -> Some (T.bool tst true)
    | B_eq _ | B_neq _ -> None
    | B_atom _ -> None

  let fresh_term self ~for_ ~pre ty =
    let u = A.Gensym.fresh_term self.gensym ~pre ty in
    Log.debugf 20
      (fun k->k "(@[sidekick.bool.proxy@ :t %a@ :for %a@])"
          T.pp u T.pp for_);
    assert (Ty.equal ty (T.ty u));
    u

  let fresh_lit (self:state) ~for_ ~mk_lit ~pre : Lit.t =
    let proxy = fresh_term ~for_ ~pre self (Ty.bool self.ty_st) in
    mk_lit proxy

  (* preprocess "ite" away *)
  let preproc_ite self si ~mk_lit ~add_clause (t:T.t) : T.t option =
    match A.view_as_bool t with
    | B_ite (a,b,c) ->
      let a = SI.simp_t si a in
      begin match A.view_as_bool a with
        | B_bool true -> Some b
        | B_bool false -> Some c
        | _ ->
          let t_ite = fresh_term self ~for_:t ~pre:"ite" (T.ty b) in
          let lit_a = mk_lit a in
          add_clause [Lit.neg lit_a; mk_lit (eq self.tst t_ite b)];
          add_clause [lit_a; mk_lit (eq self.tst t_ite c)];
          Some t_ite
      end
    | _ -> None

  (* TODO: polarity? *)
  let cnf (self:state) (_si:SI.t) ~mk_lit ~add_clause (t:T.t) : T.t option =
    let rec get_lit (t:T.t) : Lit.t =
      let t_abs, t_sign = T.abs self.tst t in
      let lit =
        match T.Tbl.find self.cnf t_abs with
        | lit -> lit (* cached *)
        | exception Not_found ->
          (* compute and cache *)
          let lit = get_lit_uncached t_abs in
          if not (T.equal (Lit.term lit) t_abs) then (
            T.Tbl.add self.cnf t_abs lit;
            Log.debugf 20
              (fun k->k "(@[sidekick.bool.add-lit@ :lit %a@ :for-t %a@])"
                  Lit.pp lit T.pp t_abs);
          );
          lit
      in
      if t_sign then lit else Lit.neg lit

    and equiv_ ~is_xor ~for_ a b : Lit.t =
      let a = get_lit a in
      let b = get_lit b in
      let a = if is_xor then Lit.neg a else a in (* [a xor b] is [(¬a) = b] *)
      let proxy = fresh_lit ~for_ ~mk_lit ~pre:"equiv_" self in
      (* proxy => a<=> b,
         ¬proxy => a xor b *)
      add_clause [Lit.neg proxy; Lit.neg a; b];
      add_clause [Lit.neg proxy; Lit.neg b; a];
      add_clause [proxy; a; b];
      add_clause [proxy; Lit.neg a; Lit.neg b];
      proxy

    and get_lit_uncached t : Lit.t =
      match A.view_as_bool t with
      | B_bool b -> mk_lit (T.bool self.tst b)
      | B_opaque_bool t -> mk_lit t
      | B_not u ->
        let lit = get_lit u in
        Lit.neg lit
      | B_and l ->
        let subs = l |> Iter.map get_lit |> Iter.to_list in
        let proxy = fresh_lit ~for_:t ~mk_lit ~pre:"and_" self in
        (* add clauses *)
        List.iter (fun u -> add_clause [Lit.neg proxy; u]) subs;
        add_clause (proxy :: List.map Lit.neg subs);
        proxy
      | B_or l ->
        let subs = l |> Iter.map get_lit |> Iter.to_list in
        let proxy = fresh_lit ~for_:t ~mk_lit ~pre:"or_" self in
        (* add clauses *)
        List.iter (fun u -> add_clause [Lit.neg u; proxy]) subs;
        add_clause (Lit.neg proxy :: subs);
        proxy
      | B_imply (args, u) ->
        (* transform into [¬args \/ u] on the fly *)
        let args = args |> Iter.map get_lit |> Iter.map Lit.neg |> Iter.to_list in
        let u = get_lit u in
        let subs = u :: args in
        (* now the or-encoding *)
        let proxy = fresh_lit ~for_:t ~mk_lit ~pre:"implies_" self in
        (* add clauses *)
        List.iter (fun u -> add_clause [Lit.neg u; proxy]) subs;
        add_clause (Lit.neg proxy :: subs);
        proxy
      | B_ite _ | B_eq _ | B_neq _ -> mk_lit t
      | B_equiv (a,b) -> equiv_ ~for_:t ~is_xor:false a b
      | B_xor  (a,b) -> equiv_ ~for_:t ~is_xor:true a b
      | B_atom u -> mk_lit u
    in
    let lit = get_lit t in
    let u = Lit.term lit in
    (* put sign back as a "not" *)
    let u = if Lit.sign lit then u else A.mk_bool self.tst (B_not u) in
    if T.equal u t then None else Some u

  (* check if new terms were added to the congruence closure, that can be turned
     into clauses *)
  let check_new_terms (self:state) si (acts:SI.actions) (_trail:_ Iter.t) : unit =
    let cc_ = SI.cc si in
    let all_terms =
      let open SI in
      CC.all_classes cc_
      |> Iter.flat_map CC.N.iter_class
      |> Iter.map CC.N.term
    in
    let cnf_of t =
      cnf self si t
        ~mk_lit:(SI.mk_lit si acts) ~add_clause:(SI.add_clause_permanent si acts)
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
