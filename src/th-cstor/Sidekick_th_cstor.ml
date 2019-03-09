
(** {1 Theory for constructors} *)

type ('c,'t) cstor_view =
  | T_cstor of 'c * 't list
  | T_other of 't

module type S = sig
  type lit
  type term

  (** Micro theory only *)
  val cc_th : Sidekick_smt.CC.Theory.t
end

module type ARG = sig
  module Fun : sig
    type t
    val equal : t -> t -> bool
end
  module T : sig
    type t
    val pp : t Fmt.printer
    val equal : t -> t -> bool
    val view_as_cstor : t -> (Fun.t,t) cstor_view
  end
end

module Make(Arg : ARG with type T.t = Sidekick_smt.Term.t)
(*   : S with type lit = Arg.Lit.t and type term = Arg.T.t *)
= struct
  module N = Sidekick_smt.Theory.CC_eq_class
  module Expl = Sidekick_smt.Theory.CC_expl
  module CC = Sidekick_smt.CC

  open Arg
  type term = T.t

  type data = {
    t: T.t;
    n: N.t;
  }
  (* associate to each class a unique constructor term in the class (if any) *)

  let pp_data out x = T.pp out x.t

  let key : (_,_,data) Sidekick_cc.Key.t = Sidekick_cc.Key.create
      ~pp:pp_data ~name:"cstor"
      ~eq:(fun x y -> T.equal x.t y.t)
      ~merge:(fun x _ -> x) ()

  type t = unit

  let on_merge (cc:CC.t) n1 tc1 n2 tc2 e_n1_n2 : unit =
    Log.debugf 5
      (fun k->k "(@[th-cstor.on_merge@ @[:c1 %a@ (term %a)@]@ @[:c2 %a@ (term %a)@]@])"
          N.pp n1 T.pp tc1.t N.pp n2 T.pp tc2.t); 
    let expl = Expl.mk_list [e_n1_n2; Expl.mk_merge n1 tc1.n; Expl.mk_merge n2 tc2.n] in
    match T.view_as_cstor tc1.t, T.view_as_cstor tc2.t with
    | T_cstor (f1, l1), T_cstor (f2, l2) ->
      if Arg.Fun.equal f1 f2 then (
        (* same function: injectivity *)
        assert (List.length l1 = List.length l2);
        List.iter2
          (fun u1 u2 -> CC.Theory.merge cc (CC.add_term cc u1) (CC.add_term cc u2) expl)
          l1 l2
      ) else (
        (* different function: disjointness *)
        CC.Theory.raise_conflict cc expl
      )
    | _ -> assert false

  let on_new_term _ n (t:T.t) =
    match T.view_as_cstor t with
    | T_cstor _ -> Some {t;n}
    | _ -> None

  let cc_th = Sidekick_smt.CC.Theory.make ~key ~on_new_term ~on_merge ()
end


(* TODO: default building of constructor terms
include Make(struct
    module Fun = Sidekick_smt.Cst
    module T = struct
      include Sidekick_smt.Term
      let[@inline] view_as_cstor t = match view t with
        | App_cst (c, args) when Fun.do_cc
        | If (a,b,c) -> T_ite (a,b,c)
        | Bool b -> T_bool b
        | _ -> T_other t
      end
    end)
   *)

