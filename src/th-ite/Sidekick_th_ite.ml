
(** {1 Theory for if-then-else} *)

type 't ite_view =
  | T_ite of 't * 't * 't
  | T_bool of bool
  | T_other of 't


module type S = sig
  type lit
  type term

  val th : Sidekick_smt.Theory.t
end

module type ARG = sig
  module T : sig
    type t
    type state
    val pp : t Fmt.printer
    val equal : t -> t -> bool
    val view_as_ite : t -> t ite_view

    module Set : CCSet.S with type elt = t
  end
  module Lit : sig
    type t
    val term : t -> T.t
    val atom : T.state -> ?sign:bool -> T.t -> t
    val pp : t Fmt.printer
  end
end

module Make(Arg : ARG with type T.state = Sidekick_smt.Term.state and type T.t = Sidekick_smt.Term.t)
  : S with type lit = Arg.Lit.t and type term = Arg.T.t
= struct
  module Th = Sidekick_smt.Theory
  module N = Th.CC_eq_class
  module Expl = Th.CC_expl
  module CC = Sidekick_smt.CC

  open Arg
  type lit = Lit.t
  type term = T.t

  type data = T.Set.t
  (* associate to each class [t] the set of [ite a b c] where [a=t] *)

  let pp_data = Fmt.(map T.Set.to_seq @@ seq ~sep:(return ",@ ") T.pp)

  let key : (_,_,data) Sidekick_cc.Key.t = Sidekick_cc.Key.create
      ~pp:pp_data ~name:"ite" ~eq:T.Set.equal ~merge:T.Set.union ()

  type t = T.state

  let on_merge (_st:t) (acts:Sidekick_smt.Theory.actions) n1 n2 e_n1_n2 : unit =
    let (module A) = acts in
    Log.debugf 5
      (fun k->k "(@[th-ite.on_merge@ :c1 %a@ :c2 %a@])" N.pp n1 N.pp n2); 
    (* check if [n1] has some [ite] parents, and if [n2] is true/false *)
    let check_ n1 n2 =
      match CC.Theory.get_data A.cc n1 key, T.view_as_ite (N.term n2) with
      | Some set, T_bool n2_true ->
        assert (not @@ T.Set.is_empty set);
        T.Set.iter
          (fun parent_1 -> match T.view_as_ite parent_1 with
             | T_ite (a1,b1,c1) ->
               let n_parent1 = CC.add_term A.cc parent_1 in
               let expl = Expl.mk_list [e_n1_n2; Expl.mk_merge n1 (CC.add_term A.cc a1)] in
               if n2_true then (
                 (* [a1 = n1 = n2 = true] so [if a1 b1 c1 = b1] *)
                 CC.Theory.merge A.cc n_parent1 (CC.add_term A.cc b1) expl
               ) else (
                 (* [a1 = n1 = n2 = false] so [if a1 b1 c1 = c1] *)
                 CC.Theory.merge A.cc n_parent1 (CC.add_term A.cc c1) expl
               )
             | _ -> assert false)
          set
      | _ -> ()
    in
    check_ n1 n2;
    check_ n2 n1;
    ()

  let on_new_term _ (acts:Sidekick_smt.Theory.actions) (t:T.t) =
    let (module A) = acts in
    match T.view_as_ite t with
    | T_ite (a,_,_) ->
      (* add [t] to parents of [a] *)
      let n_a = CC.find A.cc @@ CC.add_term A.cc a in
      CC.Theory.add_data A.cc n_a key (T.Set.singleton t)
    | _ -> ()

  let th =
    Sidekick_smt.Theory.make ~name:"ite" ~create:(fun st->st)
      ~on_merge ~final_check:(fun _ _ _ -> ())
      ~on_new_term
      ()

end


include Make(struct
    module T = struct
      include Sidekick_smt.Term
      let[@inline] view_as_ite t = match view t with
        | If (a,b,c) -> T_ite (a,b,c)
        | Bool b -> T_bool b
        | _ -> T_other t
      end
    module Lit = Sidekick_smt.Lit
    end)
