(** {2 Signatures for booleans} *)

type 'a bool_view =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'a IArray.t
  | B_or of 'a IArray.t
  | B_imply of 'a IArray.t * 'a
  | B_equiv of 'a * 'a
  | B_eq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_opaque_bool of 'a (* do not enter *)
  | B_atom of 'a

module type ARG = sig
  module S : Sidekick_core.SOLVER

  type term = S.A.Term.t

  val view_as_bool : term -> term bool_view
  (** Project the term into the boolean view *)

  val mk_bool : S.A.Term.state -> term bool_view -> term
  (** Make a term from the given boolean view *)

  val check_congruence_classes : bool
  (** Configuration: add final-check handler to verify if new boolean formulas
      are present in the congruence closure.
      Only enable if some theories are susceptible to
      create boolean formulas during the proof search. *)

  module Gensym : sig
    type t

    val create : S.A.Term.state -> t

    val fresh_term : t -> pre:string -> S.A.Ty.t -> term
    (** Make a fresh term of the given type *)
  end
end

module type S = sig
  module A : ARG

  type state

  val create : A.S.A.Term.state -> state

  val simplify : state -> A.S.Solver_internal.simplify_hook
  (** Simplify given term *)

  val cnf : state -> A.S.Solver_internal.preprocess_hook
  (** add clauses for the booleans within the term. *)

  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module Ty = A.S.A.Ty
  module T = A.S.A.Term
  module Lit = A.S.Solver_internal.Lit
  module SI = A.S.Solver_internal

  type state = {
    tst: T.state;
    simps: T.t T.Tbl.t; (* cache *)
    cnf: Lit.t T.Tbl.t; (* tseitin CNF *)
    gensym: A.Gensym.t;
  }

  let create tst : state =
    { tst; simps=T.Tbl.create 128;
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
      if IArray.exists is_false a then Some (T.bool tst false)
      else if IArray.for_all is_true a then Some (T.bool tst true)
      else None
    | B_or a ->
      if IArray.exists is_true a then Some (T.bool tst true)
      else if IArray.for_all is_false a then Some (T.bool tst false)
      else None
    | B_imply (args, u) ->
      (* turn into a disjunction *)
      let u =
        or_a tst @@
        IArray.append (IArray.map (not_ tst) args) (IArray.singleton u)
      in
      Some u
    | B_ite (a,b,c) ->
      (* directly simplify [a] so that maybe we never will simplify one
         of the branches *)
      let a = SI.Simplify.normalize simp a in
      begin match A.view_as_bool a with
        | B_bool true -> Some b
        | B_bool false -> Some c
        | _ -> None
      end
    | B_equiv (a,b) when is_true a -> Some b
    | B_equiv (a,b) when is_false a -> Some (not_ tst b)
    | B_equiv (a,b) when is_true b -> Some a
    | B_equiv (a,b) when is_false b -> Some (not_ tst a)
    | B_equiv _ -> None
    | B_eq (a,b) when T.equal a b -> Some (T.bool tst true)
    | B_eq _ -> None
    | B_atom _ -> None

  let fresh_term self ~pre ty = A.Gensym.fresh_term self.gensym ~pre ty
  let fresh_lit (self:state) ~mk_lit ~pre : Lit.t =
    let t = fresh_term ~pre self Ty.bool in
    mk_lit t

  (* TODO: polarity? *)
  let cnf (self:state) (_si:SI.t) ~mk_lit ~add_clause (t:T.t) : T.t option =
    let rec get_lit (t:T.t) : Lit.t =
      match T.Tbl.find self.cnf t with
      | lit -> lit (* cached *)
      | exception Not_found ->
        (* compute and cache *)
        let lit = get_lit_uncached t in
        if not (T.equal (Lit.term lit) (T.abs self.tst t |> fst)) then (
          T.Tbl.add self.cnf t lit;
        );
        lit
    and get_lit_uncached t : Lit.t =
      match A.view_as_bool t with
      | B_bool b -> mk_lit (T.bool self.tst b)
      | B_opaque_bool t -> mk_lit t
      | B_not u ->
        let lit = get_lit u in
        Lit.neg lit
      | B_and l ->
        let subs = IArray.to_list_map get_lit l in
        let proxy = fresh_lit ~mk_lit ~pre:"and_" self in
        (* add clauses *)
        List.iter (fun u -> add_clause [Lit.neg proxy; u]) subs;
        add_clause (proxy :: List.map Lit.neg subs);
        proxy
      | B_or l ->
        let subs = IArray.to_list_map get_lit l in
        let proxy = fresh_lit ~mk_lit ~pre:"or_" self in
        (* add clauses *)
        List.iter (fun u -> add_clause [Lit.neg u; proxy]) subs;
        add_clause (Lit.neg proxy :: subs);
        proxy
      | B_imply (args, u) ->
        let t' =
          or_a self.tst @@
          IArray.append (IArray.map (not_ self.tst) args) (IArray.singleton u) in
        get_lit t'
      | B_ite _ | B_eq _ ->
        mk_lit t
      | B_equiv (a,b) ->
        let a = get_lit a in
        let b = get_lit b in
        let proxy = fresh_lit ~mk_lit ~pre:"equiv_" self in
        (* proxy => a<=> b,
           ¬proxy => a xor b *)
        add_clause [Lit.neg proxy; Lit.neg a; b];
        add_clause [Lit.neg proxy; Lit.neg b; a];
        add_clause [proxy; a; b];
        add_clause [proxy; Lit.neg a; Lit.neg b];
        proxy
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
    let st = create (SI.tst si) in
    SI.add_simplifier si (simplify st);
    SI.add_preprocess si (cnf st);
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
