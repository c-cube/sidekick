
(** {1 Theory of Booleans} *)

open Sidekick_smt
open Solver_types

module Fmt = CCFormat

type term = Term.t

(* TODO (long term): relevancy propagation *)

(* TODO: Tseitin on the fly when a composite boolean term is asserted.
  --> maybe, cache the clause inside the literal *)

let id_not = ID.make "not"
let id_and = ID.make "and"
let id_or = ID.make "or"
let id_imply = ID.make "=>"
let id_eq = ID.make "="
let id_distinct = ID.make "distinct"

type 'a view =
  | B_not of 'a
  | B_eq of 'a * 'a
  | B_and of 'a IArray.t
  | B_or of 'a IArray.t
  | B_imply of 'a IArray.t * 'a
  | B_distinct of 'a IArray.t
  | B_atom of 'a

exception Not_a_th_term

let view_id cst_id args =
  if ID.equal cst_id id_not && IArray.length args=1 then (
    B_not (IArray.get args 0)
  ) else if ID.equal cst_id id_eq && IArray.length args=2 then (
    B_eq (IArray.get args 0, IArray.get args 1)
  ) else if ID.equal cst_id id_and then (
    B_and args
  ) else if ID.equal cst_id id_or then (
    B_or args
  ) else if ID.equal cst_id id_imply && IArray.length args >= 2 then (
    (* conclusion is stored first *)
    let len = IArray.length args in
    B_imply (IArray.sub args 1 (len-1), IArray.get args 0)
  ) else if ID.equal cst_id id_distinct then (
    B_distinct args
  ) else (
    raise Not_a_th_term
  )

let view (t:Term.t) : term view =
  match Term.view t with
  | App_cst ({cst_id; _}, args) ->
    (try view_id cst_id args with Not_a_th_term -> B_atom t)
  | _ -> B_atom t


module C = struct

  let get_ty _ _ = Ty.prop

  (* no congruence closure, except for `=` *)
  let relevant id _ _ = ID.equal id_eq id

  let abs ~self _a =
    match Term.view self with
    | App_cst ({cst_id;_}, args) when ID.equal cst_id id_not && IArray.length args=1 ->
      (* [not a] --> [a, false] *)
      IArray.get args 0, false
    | _ -> self, true

  let eval id args = match view_id id args with
    | B_not (V_bool b) -> Value.bool (not b)
    | B_and a when IArray.for_all Value.is_true a -> Value.true_
    | B_and a when IArray.exists Value.is_false a -> Value.false_
    | B_or a when IArray.exists Value.is_true a -> Value.true_
    | B_or a when IArray.for_all Value.is_false a -> Value.false_
    | B_imply (_, V_bool true) -> Value.true_
    | B_imply (a,_) when IArray.exists Value.is_false a -> Value.true_
    | B_imply (a,b) when IArray.for_all Value.is_bool a && Value.is_bool b -> Value.false_
    | B_eq (a,b) -> Value.bool @@ Value.equal a b
    | B_atom v -> v
    | B_distinct a ->
      if
        Sequence.diagonal (IArray.to_seq a)
        |> Sequence.for_all (fun (x,y) -> not @@ Value.equal x y)
      then Value.true_
      else Value.false_
    | B_not _ | B_and _ | B_or _ | B_imply _
        -> Error.errorf "non boolean value in boolean connective"

  let mk_cst ?(do_cc=false) id : Cst.t =
    {cst_id=id;
     cst_view=Cst_def { pp=None; abs; ty=get_ty; relevant; do_cc; eval=eval id; }; }

  let not = mk_cst id_not
  let and_ = mk_cst id_and
  let or_ = mk_cst id_or
  let imply = mk_cst id_imply
  let eq = mk_cst ~do_cc:true id_eq
  let distinct = mk_cst id_distinct
end

let as_id id (t:Term.t) : Term.t IArray.t option =
  match Term.view t with
  | App_cst ({cst_id; _}, args) when ID.equal id cst_id -> Some args
  | _ -> None

(* flatten terms of the given ID *)
let flatten_id id (l:Term.t list) : Term.t list =
  CCList.flat_map
    (fun t -> match as_id id t with
       | Some args -> IArray.to_list args
       | None -> [t])
    l

let and_l st l =
  match flatten_id id_and l with
  | [] -> Term.true_ st
  | l when List.exists Term.is_false l -> Term.false_ st
  | [x] -> x
  | args -> Term.app_cst st C.and_ (IArray.of_list args)

let or_l st l =
  match flatten_id id_or l with
  | [] -> Term.false_ st
  | l when List.exists Term.is_true l -> Term.true_ st
  | [x] -> x
  | args -> Term.app_cst st C.or_ (IArray.of_list args)

let and_ st a b = and_l st [a;b]
let or_ st a b = or_l st [a;b]

let eq st a b =
  if Term.equal a b then Term.true_ st
  else (
    let a,b = if Term.id a > Term.id b then b, a else a, b in
    Term.app_cst st C.eq (IArray.doubleton a b)
  )

let not_ st a =
  match as_id id_not a, Term.view a with
  | _, Bool false -> Term.true_ st
  | _, Bool true -> Term.false_ st
  | Some args, _ ->
    assert (IArray.length args = 1);
    IArray.get args 0
  | None, _ -> Term.app_cst st C.not (IArray.singleton a)

let neq st a b = not_ st @@ eq st a b

let imply st xs y = match xs with
  | [] -> y
  | _ -> Term.app_cst st C.imply (IArray.of_list @@ y :: xs)

let distinct st = function
  | [] | [_] -> Term.true_ st
  | xs -> Term.app_cst st C.distinct (IArray.of_list xs)

module Lit = struct
  include Lit
  let eq tst a b = Lit.atom ~sign:true (eq tst a b)
  let neq tst a b = Lit.atom ~sign:false (neq tst a b)
end

type t = {
  tst: Term.state;
  acts: Theory.actions;
}

let tseitin (self:t) (lit:Lit.t) (lit_t:term) (v:term view) : unit =
  Log.debugf 5 (fun k->k "(@[th_bool.tseitin@ %a@])" Lit.pp lit);
  let (module A) = self.acts in
  match v with
  | B_atom _ -> ()
  | B_not _ -> assert false (* normalized *)
  | B_eq (t,u) ->
    if Lit.sign lit then (
      A.propagate_eq t u [lit]
    ) else (
      A.propagate_distinct [t;u] ~neq:lit_t lit
    )
  | B_distinct l ->
    let l = IArray.to_list l in
    if Lit.sign lit then (
      A.propagate_distinct l ~neq:lit_t lit
    ) else (
      (* TODO: propagate pairwise equalities? *)
      Error.errorf "cannot process negative distinct lit %a" Lit.pp lit;
    )
  | B_and subs ->
    if Lit.sign lit then (
      (* propagate [lit => subs_i] *)
      IArray.iter
        (fun sub ->
           let sublit = Lit.atom sub in
           A.propagate sublit [lit])
        subs
    ) else (
      (* propagate [¬lit => ∨_i ¬ subs_i] *)
      let subs = IArray.to_list subs in
      let c = Lit.neg lit :: List.map (Lit.atom ~sign:false) subs in
      A.add_local_axiom (IArray.of_list c)
    )
  | B_or subs ->
    if Lit.sign lit then (
      (* propagate [lit => ∨_i subs_i] *)
      let subs = IArray.to_list subs in
      let c = Lit.neg lit :: List.map (Lit.atom ~sign:true) subs in
      A.add_local_axiom (IArray.of_list c)
    ) else (
      (* propagate [¬lit => ¬subs_i] *)
      IArray.iter
        (fun sub ->
           let sublit = Lit.atom ~sign:false sub in
           A.propagate sublit [lit])
        subs
    )
  | B_imply (guard,concl) ->
    if Lit.sign lit then (
      (* propagate [lit => ∨_i ¬guard_i ∨ concl] *)
      let guard = IArray.to_list guard in
      let c = Lit.atom concl :: Lit.neg lit :: List.map (Lit.atom ~sign:false) guard in
      A.add_local_axiom (IArray.of_list c)
    ) else (
      (* propagate [¬lit => ¬concl] *)
      A.propagate (Lit.atom ~sign:false concl) [lit];
      (* propagate [¬lit => ∧_i guard_i] *)
      IArray.iter
        (fun sub ->
           let sublit = Lit.atom ~sign:true sub in
           A.propagate sublit [lit])
        guard
    )

let on_assert (self:t) (lit:Lit.t) =
  match Lit.view lit with
  | Lit.Lit_atom t ->
    begin match view t with
      | B_atom _ -> ()
      | v -> tseitin self lit t v
    end
  | _ -> ()

let final_check _ _ : unit = ()

let th =
  let make tst acts =
    let st = {tst;acts} in
    Theory.make_st
      ~on_assert
      ~final_check
      ?mk_model:None (* entirely interpreted *)
      ~st
      ()
  in
  Theory.make ~name:"boolean" ~make ()
