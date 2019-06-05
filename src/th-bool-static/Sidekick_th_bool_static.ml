(** {2 Signatures for booleans} *)

type 'a bool_view =
  | B_not of 'a
  | B_and of 'a IArray.t
  | B_or of 'a IArray.t
  | B_imply of 'a IArray.t * 'a
  | B_equiv of 'a * 'a
  | B_eq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_atom of 'a

type ('tst,'a) non_bool_view =
  | NB_ite of 'a * 'a * 'a
  | NB_functor of 'a IArray.t * ('tst -> 'a IArray.t -> 'a)
  | NB_bool of 'a (* boolean subterm *)

module type ARG = sig
  module S : Sidekick_core.SOLVER

  type term = S.A.Term.t

  val view_as_bool : term -> term bool_view
  (** Project the term into the boolean view *)

  val view_as_non_bool : term -> (S.A.Term.state,term) non_bool_view
  (** Project the term into the boolean view *)

  val mk_bool : S.A.Term.state -> term bool_view -> term
  (** Make a term from the given boolean view *)

  val mk_ite : S.A.Term.state -> term -> term -> term -> term

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

  type state

  val create : T.state -> state

  val simplify : state -> T.t -> T.t
  (** Simplify given term *)

  val cnf : state -> T.t -> A.S.A.Lit.t list Vec.t
  (** add clauses for the booleans within the term. *)

  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module Ty = A.S.A.Ty
  module T = A.S.A.Term
  module Lit = A.S.A.Lit

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
    
  let simplify (self:state) (t:T.t) : T.t =
    let rec aux t =
      let tst = self.tst in
      match T.Tbl.find self.simps t with
      | u -> u
      | exception Not_found ->
        let u, cache =
          match A.view_as_bool t with
          | B_not u -> not_ tst (aux u), false
          | B_and a ->
            let a = IArray.map aux a in
            let u = 
              if IArray.exists is_false a then T.bool tst false
              else if IArray.for_all is_true a then T.bool tst true
              else and_a tst a
            in
            u, true
          | B_or a ->
            let a = IArray.map aux a in
            let u = 
              if IArray.exists is_true a then T.bool tst true
              else if IArray.for_all is_false a then T.bool tst false
              else or_a tst a
            in
            u, true
          | B_imply (args, u) ->
            (* turn into a disjunction *)
            let u =
              aux @@ or_a tst @@
              IArray.append (IArray.map (not_ tst) args) (IArray.singleton u)
            in
            u, true
          | B_ite (a,b,c) ->
            let a = aux a in
            begin match T.as_bool a with
              | Some true -> aux b
              | Some false -> aux c
              | _ -> ite tst a (aux b) (aux c)
            end, true
          | B_equiv (a,b) ->
            let u = equiv tst (aux a) (aux b) in
            u, true
          | B_eq (a,b) ->
            let u = eq tst (aux a) (aux b) in
            u, true
          | B_atom a ->
            begin match A.view_as_non_bool a with
              | NB_bool _ -> assert false
              | NB_ite (a,b,c) ->
                A.mk_ite tst (aux a) (aux b) (aux c), true
              | NB_functor (args, mk) ->
                mk tst (IArray.map aux args), true
            end
        in
        if cache then (
          T.Tbl.add self.simps t u; (* cache rewriting step *)
        );
        u
    in
    let u = aux t in
    if not (T.equal t u) then (
      Log.debugf 5
        (fun k->k "(@[th-bool.simplified@ :from %a@ :to %a@])" T.pp t T.pp u);
    );
    u

  let fresh_term self ~pre ty = A.Gensym.fresh_term self.gensym ~pre ty
  let fresh_lit (self:state) ~pre : Lit.t =
    let t = fresh_term ~pre self Ty.bool in
    Lit.atom self.tst t

  (* TODO: polarity *)
  let cnf (self:state) (t:T.t) : Lit.t list Vec.t =
    let cs: Lit.t list Vec.t = Vec.create() in
    let add_clause lits = Vec.push cs lits in
    let rec aux_bool (t:T.t) : Lit.t =
      let tst = self.tst in
      match T.Tbl.find self.cnf t with
      | u -> u
      | exception Not_found ->
        let lit, cache =
          match A.view_as_bool t with
          | B_not u ->
            let lit = aux_bool u in
            Lit.neg lit, false
          | B_and l ->
            let subs = IArray.to_list_map aux_bool l in
            let proxy = fresh_lit ~pre:"and_" self in
            (* add clauses *)
            List.iter (fun u -> add_clause [Lit.neg proxy; u]) subs;
            add_clause (proxy :: List.map Lit.neg subs);
            proxy, true
          | B_or l ->
            let subs = IArray.to_list_map aux_bool l in
            let proxy = fresh_lit ~pre:"or_" self in
            (* add clauses *)
            List.iter (fun u -> add_clause [Lit.neg u; proxy]) subs;
            add_clause (Lit.neg proxy :: subs);
            proxy, true
          | B_imply (args, u) ->
            let t' =
              or_a tst @@
              IArray.append (IArray.map (not_ tst) args) (IArray.singleton u) in
            aux_bool t', true
          | B_ite _ ->
            Lit.atom tst (aux_t t), true
          | B_eq _ ->
            Lit.atom tst (aux_t t), true
          | B_equiv (a,b) ->
            Format.printf "@[cnf: equiv@ %a@ and %a@]@." T.pp a T.pp b;
            let a = aux_bool a in
            let b = aux_bool b in
            let proxy = fresh_lit ~pre:"equiv_" self in
            (* proxy => a<=> b,
               ¬proxy => a xor b *)
            add_clause [Lit.neg proxy; Lit.neg a; b];
            add_clause [Lit.neg proxy; Lit.neg b; a];
            add_clause [proxy; a; b];
            add_clause [proxy; Lit.neg a; Lit.neg b];
            proxy, true
          | B_atom u ->
            Lit.atom tst (aux_t u), false
        in
        if cache then (
          T.Tbl.add self.cnf t lit; (* cache rewriting step *)
        );
        lit

    and aux_t (t:T.t) : T.t =
      let tst = self.tst in
      match A.view_as_non_bool t with
      | NB_ite (a,b,c) ->
        begin match T.Tbl.find self.cnf_ite t with
          | u -> u
          | exception Not_found ->
            let a = aux_bool a in
            let b = aux_t b in
            let c = aux_t c in
            let proxy = fresh_term ~pre:"ite_" self (T.ty b) in
            T.Tbl.add self.cnf_ite t proxy;
            (* add clauses: [a => proxy=b], [¬a => proxy=c] *)
            add_clause [Lit.neg a; Lit.atom tst (eq tst proxy b)];
            add_clause [a; Lit.atom tst (eq tst proxy c)];
            proxy
        end
      | NB_bool _ -> Lit.term (aux_bool t)
      | NB_functor (args, mk) ->
        (* pass through *)
        let args = IArray.map aux_t args in
        mk tst args
    in
    (* traverse [t] to produce clauses *)
    if Ty.is_bool (T.ty t) then (
      let top = aux_bool t in
      add_clause [top]; (* also add a clause standing for [t = true] *)
    ) else (
      ignore (aux_t t: T.t);
    );
    cs

  (* TODO: register [cnf] as a clausifier, register [simplify] as a
     preprocessor *)
  let create_and_setup _si = ()

  let theory =
    A.S.mk_theory
      ~name:"th-bool"
      ~create_and_setup
      ()
end
