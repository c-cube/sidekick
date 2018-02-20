
(** {1 Theory of Booleans} *)

open Dagon_smt

module Fmt = CCFormat

type term = Term.t

(* TODO (long term): relevancy propagation *)

(* TODO: Tseitin on the fly when a composite boolean term is asserted.
  --> maybe, cache the clause inside the literal *)

(* TODO: in theory (or terms?) have a way to evaluate custom terms
   (like formulas) in a given model, for checking models *)

type 'a builtin =
  | B_not of 'a
  | B_eq of 'a * 'a
  | B_and of 'a list
  | B_or of 'a list
  | B_imply of 'a list * 'a
  | B_distinct of 'a list

let fold_map_builtin
    (f:'a -> 't -> 'b * 'u) (acc:'a) (b:'t builtin): 'b * 'u builtin =
  let fold_binary acc a b =
    let acc, a = f acc a in
    let acc, b = f acc b in
    acc, a, b
  in
  match b with
    | B_not t ->
      let acc, t' = f acc t in
      acc, B_not t'
    | B_and l ->
      let acc, l = CCList.fold_map f acc l in
      acc, B_and l
    | B_or l ->
      let acc, l = CCList.fold_map f acc l in
      acc, B_or l
    | B_eq (a,b) ->
      let acc, a, b = fold_binary acc a b in
      acc, B_eq (a, b)
    | B_distinct l ->
      let acc, l = CCList.fold_map f acc l in
      acc, B_distinct l
    | B_imply (a,b) ->
      let acc, a = CCList.fold_map f acc a in
      let acc, b = f acc b in
      acc, B_imply (a, b)

let map_builtin f b =
  let (), b = fold_map_builtin (fun () t -> (), f t) () b in
  b

let builtin_to_seq b yield = match b with
  | B_not t -> yield t
  | B_or l | B_and l | B_distinct l -> List.iter yield l
  | B_imply (a,b) -> List.iter yield a; yield b
  | B_eq (a,b) -> yield a; yield b

type 'a Term.custom +=
  | Builtin of {
      view: 'a builtin;
      (* TODO: bool value + explanation *)
      (* TODO: caching of Tseiting *)
    }

module TC = struct
  let hash sub_hash = function
    | Builtin {view; _} ->
      begin match view with
        | B_not a -> Hash.combine2 20 (sub_hash a)
        | B_and l -> Hash.combine2 21 (Hash.list sub_hash l)
        | B_or l -> Hash.combine2 22 (Hash.list sub_hash l)
        | B_imply (l1,t2) -> Hash.combine3 23 (Hash.list sub_hash l1) (sub_hash t2)
        | B_eq (t1,t2) -> Hash.combine3 24 (sub_hash t1) (sub_hash t2)
        | B_distinct l -> Hash.combine2 26 (Hash.list sub_hash l)
      end
    | _ -> assert false

  let eq sub_eq a b = match a, b with
    | Builtin {view=b1; _}, Builtin {view=b2;_} ->
      begin match b1, b2 with
        | B_not a1, B_not a2 -> sub_eq a1 a2
        | B_and l1, B_and l2
        | B_or l1, B_or l2 -> CCEqual.list sub_eq l1 l2
        | B_distinct l1, B_distinct l2 -> CCEqual.list sub_eq l1 l2
        | B_eq (a1,b1), B_eq (a2,b2) -> sub_eq a1 a2 && sub_eq b1 b2
        | B_imply (a1,b1), B_imply (a2,b2) -> CCEqual.list sub_eq a1 a2 && sub_eq b1 b2
        | B_not _, _ | B_and _, _ | B_eq _, _
        | B_or _, _ | B_imply _, _ | B_distinct _, _
          -> false
      end
    | Builtin _, _
    | _, Builtin _ -> false
    | _ -> assert false

  let pp sub_pp out = function
    | Builtin {view=b;_} ->
      begin match b with
        | B_not t -> Fmt.fprintf out "(@[<hv>not@ %a@])" sub_pp t
        | B_and l ->
          Fmt.fprintf out "(@[<hv>and@ %a@])" (Util.pp_list sub_pp) l
        | B_or l ->
          Fmt.fprintf out "(@[<hv>or@ %a@])" (Util.pp_list sub_pp) l
        | B_imply (a,b) ->
          Fmt.fprintf out "(@[<hv1>=>@ %a@ %a@])" (Util.pp_list sub_pp) a sub_pp b
        | B_eq (a,b) ->
          Fmt.fprintf out "(@[<hv1>=@ %a@ %a@])" sub_pp a sub_pp b
        | B_distinct l ->
          Fmt.fprintf out "(@[<hv1>distinct@ %a@])" (Util.pp_list sub_pp) l
      end
    | _ -> assert false

  let get_ty _ = function
    | Builtin _ -> Ty.prop
    | _ -> assert false

  (* no Shostak for builtins, everything goes through clauses to
     the SAT solver *)
  let is_semantic = function
    | Builtin {view=_;_} -> false
    | _ -> assert false

  let solve _ _ = assert false (* never called *)

  let sub = function
    | Builtin {view;_} -> builtin_to_seq view
    | _ -> assert false

  let relevant = function
    | Builtin _ -> Sequence.empty (* no congruence closure *)
    | _ -> assert false

  let abs ~self = function
    | Builtin {view=B_not b; _} -> b, false
    | _ -> self, true

  let subst _ _ = assert false (* no congruence *)

  let explain _eq _ _ = assert false (* no congruence *)

  let tc : Term_cell.tc = {
    Term_cell.
    tc_t_pp = pp;
    tc_t_equal = eq;
    tc_t_hash = hash;
    tc_t_ty = get_ty;
    tc_t_is_semantic = is_semantic;
    tc_t_solve = solve;
    tc_t_sub = sub;
    tc_t_abs = abs;
    tc_t_relevant = relevant;
    tc_t_subst = subst;
    tc_t_explain = explain
  }
end

let tc = TC.tc

module T_cell = struct
  type t = Term_cell.t

  let builtin b =
    let mk_ x = Term_cell.custom ~tc (Builtin {view=x}) in
    (* normalize a bit *)
    begin match b with
      | B_imply ([], x) -> Term.cell x
      | B_eq (a,b) when Term.equal a b -> Term_cell.true_
      | B_eq (a,b) when Term.id a > Term.id b -> mk_ @@ B_eq (b,a)
      | B_and l ->
        begin try
            let l = CCList.flat_map
                (function
                  | {Term.term_cell=Term.Custom {view=Builtin {view=B_and l';_};_};_} -> l'
                  | {Term.term_cell=Term.Bool false;_} -> raise Exit
                  | x->[x])
                l
            in
            mk_ @@ B_and l
          with Exit -> Term_cell.false_
        end
      | B_or l ->
        begin try
            let l = CCList.flat_map
                (function
                  | {Term.term_cell=Term.Custom {view=Builtin {view=B_or l';_};_};_} -> l'
                  | {Term.term_cell=Term.Bool true;_} -> raise Exit
                  | x->[x])
                l
            in
            mk_ @@ B_or l
          with Exit -> Term_cell.true_
        end
      | _ -> mk_ b
    end

  let not_ t = match Term.cell t with
    | Term_cell.Custom {view=Builtin {view=B_not t';_};_} -> Term.cell t'
    | _ -> builtin (B_not t)

  let and_ l = builtin (B_and l)
  let or_ l = builtin (B_or l)
  let imply a b = builtin (B_imply (a,b))
  let eq a b = builtin (B_eq (a,b))
  let distinct = function
    | [] | [_] -> Term_cell.true_
    | l -> builtin (B_distinct l)
  let neq a b = distinct [a;b]
end

let make = Term.make

let not_ st t = make st (T_cell.not_ t)

let and_l st = function
  | [] -> Term.true_ st
  | [t] -> t
  | l -> make st (T_cell.and_ l)

let or_l st = function
  | [] -> Term.false_ st
  | [t] -> t
  | l -> make st (T_cell.or_ l)

let and_ st a b = and_l st [a;b]
let or_ st a b = or_l st [a;b]
let imply st a b = match a, Term.cell b with
  | [], _ -> b
  | _::_, Term_cell.Custom {view=Builtin {view=B_imply (a',b')}; _} ->
    make st (T_cell.imply (CCList.append a a') b')
  | _ -> make st (T_cell.imply a b)
let eq st a b = make st (T_cell.eq a b)
let distinct st l = make st (T_cell.distinct l)
let neq st a b = make st (T_cell.neq a b)
let builtin st b = make st (T_cell.builtin b)

module Lit = struct
  include Lit
  let eq tst a b = Lit.atom ~sign:true (eq tst a b)
  let neq tst a b = Lit.atom ~sign:false (neq tst a b)
end

type t = {
  tst: Term.state;
  acts: Theory.actions;
}

let tseitin (self:t) (lit:Lit.t) (b:term builtin) : unit =
  Log.debugf 5 (fun k->k "(@[th_bool.tseitin@ %a@])" Lit.pp lit);
  match b with
  | B_not _ -> assert false (* normalized *)
  | B_eq (t,u) ->
    self.acts.Theory.propagate_eq t u (Explanation.lit lit)
  | B_distinct _ ->
    assert false (* TODO: go to CC, or custom ineq? *)
  | B_and subs ->
    if Lit.sign lit then (
      (* propagate [lit => subs_i] *)
      let expl = Bag.return (Explanation.lit lit) in
      List.iter
        (fun sub ->
           let sublit = Lit.atom sub in
           self.acts.Theory.propagate sublit expl)
        subs
    ) else (
      (* propagate [¬lit => ∨_i ¬ subs_i] *)
      let c = lit :: List.map (Lit.atom ~sign:false) subs in
      self.acts.Theory.add_local_axiom (IArray.of_list c)
    )
  | B_or subs ->
    if Lit.sign lit then (
      (* propagate [lit => ∨_i subs_i] *)
      let c = lit :: List.map (Lit.atom ~sign:true) subs in
      self.acts.Theory.add_local_axiom (IArray.of_list c)
    ) else (
      (* propagate [¬lit => ¬subs_i] *)
      let expl = Bag.return (Explanation.lit lit) in
      List.iter
        (fun sub ->
           let sublit = Lit.atom ~sign:false sub in
           self.acts.Theory.propagate sublit expl)
        subs
    )
  | B_imply (guard,concl) ->
    if Lit.sign lit then (
      (* propagate [lit => ∨_i ¬guard_i ∨ concl] *)
      let c = lit :: Lit.atom concl :: List.map (Lit.atom ~sign:false) guard in
      self.acts.Theory.add_local_axiom (IArray.of_list c)
    ) else (
      let expl = Bag.return (Explanation.lit lit) in
      (* propagate [¬lit => ¬concl] *)
      self.acts.Theory.propagate (Lit.atom ~sign:false concl) expl;
      (* propagate [¬lit => ∧_i guard_i] *)
      List.iter
        (fun sub ->
           let sublit = Lit.atom ~sign:true sub in
           self.acts.Theory.propagate sublit expl)
        guard
    )

let on_assert (self:t) (lit:Lit.t) =
  Log.debugf 5 (fun k->k "(@[th_bool.on_assert@ %a@])" Lit.pp lit);
  match Lit.view lit with
  | Lit.Lit_atom { Term.term_cell=Term.Custom{view=Builtin {view=b};_}; _ } ->
    tseitin self lit b
  | _ -> ()

let final_check _ _ : unit =
  Log.debug 5 "(th_bool.final_check)"

let th =
  let make tst acts =
    let st = {tst;acts} in
    Theory.make_st
      ~on_assert
      ~final_check
      ~st
      ()
  in
  Theory.make ~name:"boolean" ~make ()
