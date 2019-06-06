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
  | B_atom of 'a

module type ARG = sig
  module S : Sidekick_core.SOLVER

  type term = S.A.Term.t

  val view_as_bool : term -> term bool_view
  (** Project the term into the boolean view *)

  val mk_bool : S.A.Term.state -> term bool_view -> term
  (** Make a term from the given boolean view *)

  module Gensym : sig
    type t

    val create : S.A.Term.state -> t

    val fresh_term : t -> pre:string -> S.A.Ty.t -> term
    (** Make a fresh term of the given type *)
  end
end

module type S = sig
  module A : ARG
  module T = A.S.A.Term
  module SI = A.S.Solver_internal

  type state

  val create : T.state -> state

  val simplify : state -> SI.simplify_hook
  (** Simplify given term *)

  val cnf : state -> SI.preprocess_hook
  (** add clauses for the booleans within the term. *)

  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module Ty = A.S.A.Ty
  module T = A.S.A.Term
  module Lit = A.S.A.Lit
  module SI = A.S.Solver_internal

  type state = {
    tst: T.state;
    simps: T.t T.Tbl.t; (* cache *)
    cnf: Lit.t T.Tbl.t; (* tseitin CNF *)
    cnf_ite: T.t T.Tbl.t; (* proxies for "ite" *)
    gensym: A.Gensym.t;
  }

  let create tst : state =
    { tst; simps=T.Tbl.create 128;
      cnf=T.Tbl.create 128; cnf_ite=T.Tbl.create 32;
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
  let fresh_lit (self:state) ~pre : Lit.t =
    let t = fresh_term ~pre self Ty.bool in
    Lit.atom self.tst t

  (* TODO: polarity? *)
  let cnf (self:state) (solver:SI.t) (acts:SI.actions) (t:T.t) : T.t option =
    let add_clause lits = SI.add_clause_permanent solver acts lits in
    let rec get_lit (t:T.t) : Lit.t =
      match A.view_as_bool t with
      | B_bool b -> Lit.atom self.tst ~sign:b (T.bool self.tst true)
      | B_not u ->
        let lit = get_lit u in
        Lit.neg lit
      | B_and l ->
        let subs = IArray.to_list_map get_lit l in
        let proxy = fresh_lit ~pre:"and_" self in
        (* add clauses *)
        List.iter (fun u -> add_clause [Lit.neg proxy; u]) subs;
        add_clause (proxy :: List.map Lit.neg subs);
        proxy
      | B_or l ->
        let subs = IArray.to_list_map get_lit l in
        let proxy = fresh_lit ~pre:"or_" self in
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
        Lit.atom self.tst t
      | B_equiv (a,b) ->
        Format.printf "@[cnf: equiv@ %a@ and %a@]@." T.pp a T.pp b;
        let a = get_lit a in
        let b = get_lit b in
        let proxy = fresh_lit ~pre:"equiv_" self in
        (* proxy => a<=> b,
           ¬proxy => a xor b *)
        add_clause [Lit.neg proxy; Lit.neg a; b];
        add_clause [Lit.neg proxy; Lit.neg b; a];
        add_clause [proxy; a; b];
        add_clause [proxy; Lit.neg a; Lit.neg b];
        proxy
      | B_atom u -> Lit.atom self.tst u
    in
    let lit = get_lit t in
    let u = Lit.term lit in
    if T.equal u t then None else Some u

  let create_and_setup si =
    Log.debug 2 "(th-bool.setup)";
    let st = create (SI.tst si) in
    SI.add_simplifier si (simplify st);
    SI.add_preprocess si (cnf st);
    st

  let theory =
    A.S.mk_theory
      ~name:"th-bool"
      ~create_and_setup
      ()
end
