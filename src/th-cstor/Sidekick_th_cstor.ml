(** {1 Theory for constructors} *)

type ('c,'t) cstor_view =
  | T_cstor of 'c * 't list
  | T_other of 't

let name = "th-cstor"

module type ARG = sig
  module S : Sidekick_core.SOLVER
  val view_as_cstor : S.A.Term.t -> (S.A.Fun.t, S.A.Term.t) cstor_view
end

module type S = sig
  module A : ARG
  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module SI = A.S.Solver_internal
  module T = A.S.A.Term
  module N = SI.N
  module Fun = A.S.A.Fun
  module Expl = SI.Expl

  type cstor_repr = {
    t: T.t;
    n: N.t;
  }
  (* associate to each class a unique constructor term in the class (if any) *)

  (* TODO 
  module N_tbl = Backtrackable_tbl.Make(N)
     *)
  module N_tbl = CCHashtbl.Make(N)

  type t = {
    cstors: T.t N_tbl.t; (* repr -> cstor for the class *)
    (* TODO: also allocate a bit in CC to filter out quickly classes without cstors *)
  }

  let on_merge (solver:SI.t) n1 tc1 n2 tc2 e_n1_n2 : unit =
    Log.debugf 5
      (fun k->k "(@[th-cstor.on_merge@ @[:c1 %a@ (term %a)@]@ @[:c2 %a@ (term %a)@]@])"
          N.pp n1 T.pp tc1.t N.pp n2 T.pp tc2.t); 
    let expl = Expl.mk_list [e_n1_n2; Expl.mk_merge n1 tc1.n; Expl.mk_merge n2 tc2.n] in
    match A.view_as_cstor tc1.t, A.view_as_cstor tc2.t with
    | T_cstor (f1, l1), T_cstor (f2, l2) ->
      (* merging two constructor terms: injectivity + disjointness checks *)
      if Fun.equal f1 f2 then (
        (* same function: injectivity *)
        assert (List.length l1 = List.length l2);
        List.iter2
          (fun u1 u2 -> SI.cc_merge_t solver u1 u2 expl)
          l1 l2
      ) else (
        (* different function: disjointness *)
        SI.cc_raise_conflict solver expl
      )
    | _ -> assert false

  (* attach data to constructor terms *)
  let on_new_term _ n (t:T.t) =
    match A.view_as_cstor t with
    | T_cstor _ -> Some {t;n}
    | _ -> None

  let create_and_setup (_solver:SI.t) : t =
    let self = {
      cstors=N_tbl.create 32;
    } in
    (* TODO
    SI.on_cc_merge solver on_merge;
    SI.on_cc_new_term solver on_new_term;
       *)
    self

  let theory = A.S.mk_theory ~name ~create_and_setup ()
end
