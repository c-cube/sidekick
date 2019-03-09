
module Term = Sidekick_smt.Term
module Theory = Sidekick_smt.Theory

module type ARG = sig
  module T : sig
    type t
    type state
    val pp : t Fmt.printer
    val equal : t -> t -> bool
    val hash : t -> int
    val as_distinct : t -> t Sequence.t option
    val mk_eq : state -> t -> t -> t
  end
  module Lit : sig
    type t
    val term : t -> T.t
    val neg : t -> t
    val sign : t -> bool
    val compare : t -> t -> int
    val atom : T.state -> ?sign:bool -> T.t -> t
    val pp : t Fmt.printer
  end
end
  
module type S = sig
  type term
  type term_state
  type lit

  type data
  val key : (term, lit, data) Sidekick_cc.Key.t
  val th : Sidekick_smt.Theory.t
end

module Make(A : ARG with type Lit.t = Sidekick_smt.Lit.t
                     and type T.t = Sidekick_smt.Term.t
                     and type T.state = Sidekick_smt.Term.state) = struct
  module T = A.T
  module Lit = A.Lit
  module IM = CCMap.Make(Lit)

  type term = T.t
  type term_state = T.state
  type lit = A.Lit.t
  type data = term IM.t (* "distinct" lit -> term appearing under it*)

  let key : (term,lit,data) Sidekick_cc.Key.t =
    let merge m1 m2 =
      IM.merge_safe m1 m2
        ~f:(fun _ pair -> match pair with
            | `Left x | `Right x -> Some x
            | `Both (x,_) -> Some x)
    and eq = IM.equal T.equal
    and pp out m =
      Fmt.fprintf out
        "{@[%a@]}" Fmt.(seq ~sep:(return ",@ ") @@ pair Lit.pp T.pp) (IM.to_seq m)
    in
    Sidekick_cc.Key.create
      ~pp
      ~name:"distinct"
      ~merge ~eq ()

  (* micro theory *)
  module Micro(CC : Sidekick_cc.Congruence_closure.S
               with type term = T.t
                and type lit = Lit.t
                and module Key = Sidekick_cc.Key) = struct
    exception E_exit

    let on_merge cc n1 m1 n2 m2 expl12 =
      try
        let _i =
          IM.merge
            (fun lit o1 o2 ->
               match o1, o2 with
               | Some t1, Some t2 ->
                 (* conflict! two terms under the same "distinct" [lit]
                    are merged, where [lit = distinct(t1,t2,…)].
                    The conflict is:
                    [lit, t1=n1, t2=n2, expl-merge(n1,n2) ==> false]
                 *)
                 assert (not @@ T.equal t1 t2);
                 let expl = CC.Expl.mk_list
                     [expl12;
                      CC.Expl.mk_lit lit;
                      CC.Expl.mk_merge n1 (CC.Theory.add_term cc t1);
                      CC.Expl.mk_merge n2 (CC.Theory.add_term cc t2);
                     ] in
                 CC.Theory.raise_conflict cc expl;
                 raise_notrace E_exit
               | _ -> None)
            m1 m2
        in
        ()
      with E_exit -> ()

    let on_new_term _ _ _ = None

    let th =
      CC.Theory.make ~key ~on_merge ~on_new_term ()
  end

  module T_tbl = CCHashtbl.Make(T)
  type st = {
    tst: T.state;
    expanded: unit T_tbl.t; (* negative "distinct" that have been case-split on *)
  }

  let create tst : st = { expanded=T_tbl.create 12; tst; }

  let pp_c out c = Fmt.fprintf out "(@[<hv>%a@])" (Util.pp_list Lit.pp) c

  module CC = Sidekick_smt.CC

  let process_lit (st:st) (acts:Theory.actions) (lit:Lit.t) (lit_t:term) (subs:term Sequence.t) : unit =
    let (module A) = acts in
    Log.debugf 5 (fun k->k "(@[th_distinct.process@ %a@])" Lit.pp lit);
    let add_axiom c = A.add_persistent_axiom c in
    let cc = A.cc in
    if Lit.sign lit then (
      (* assert [distinct subs], so we update the node of each [t in subs]
         with [lit] *)
      (* FIXME: detect if some subs are already equal *)
      subs
        (fun sub ->
          let n = CC.Theory.add_term cc sub in
          CC.Theory.add_data cc n key (IM.singleton lit sub));
    ) else if not @@ T_tbl.mem st.expanded lit_t then (
      (* add clause [distinct t1…tn ∨ ∨_{i,j>i} t_i=j] *)
      T_tbl.add st.expanded lit_t ();
      let l = Sequence.to_list subs in
      let c =
        Sequence.diagonal_l l
        |> Sequence.map (fun (t,u) -> Lit.atom st.tst @@ T.mk_eq st.tst t u)
        |> Sequence.to_rev_list
      in
      let c = Lit.neg lit :: c in
      Log.debugf 5 (fun k->k "(@[tseitin.distinct.case-split@ %a@])" pp_c c);
      add_axiom c
    )

  let partial_check st (acts:Theory.actions) lits : unit =
    lits
      (fun lit ->
         let t = Lit.term lit in
         match T.as_distinct t with
         | None -> ()
         | Some subs -> process_lit st acts lit t subs)

  let th =
    Sidekick_smt.Theory.make
      ~name:"distinct"
      ~partial_check
      ~final_check:(fun _ _ _ -> ())
      ~create ()
end

module Arg = struct
  open Sidekick_smt
  open Sidekick_smt.Solver_types

  let id_distinct = ID.make "distinct"

  let relevant _id _ _ = true
  let get_ty _ _ = Ty.prop
  let abs ~self _a = self, true

  module T = struct
    include Term
    let mk_eq = eq

    let as_distinct t : _ option =
      match view t with
      | App_cst ({cst_id;_}, args) when ID.equal cst_id id_distinct ->
        Some (IArray.to_seq args)
      | _ -> None
  end

  module Lit = Sidekick_smt.Lit

  let eval args =
    let module Value = Sidekick_smt.Value in
    if
      Sequence.diagonal (IArray.to_seq args)
      |> Sequence.for_all (fun (x,y) -> not @@ Value.equal x y)
    then Value.true_
    else Value.false_

  let c_distinct =
    {cst_id=id_distinct;
     cst_view=Cst_def {
         pp=None; abs; ty=get_ty; relevant; do_cc=true; eval; }; }

  let distinct st a =
    if IArray.length a <= 1
    then T.true_ st
    else T.app_cst st c_distinct a

  let distinct_l st = function
    | [] | [_] -> T.true_ st
    | xs -> distinct st (IArray.of_list xs)
end

let distinct = Arg.distinct
let distinct_l = Arg.distinct_l

include Make(Arg)
