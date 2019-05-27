
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
  module Solver = A.S.Internal
  module T = A.S.A.Term
  module N = Solver.N
  module Fun = A.S.A.Fun
  module Expl = Solver.Expl

  type data = {
    t: T.t;
    n: N.t;
  }
  (* associate to each class a unique constructor term in the class (if any) *)

  module Data = struct
    type t = data
    let pp out x = T.pp out x.t
    (* let equal x y = T.equal x.t y.t *)
    let merge x _ = x
  end

  type t = {
    k: data Solver.Key.t;
  }

  let on_merge (solver:Solver.t) n1 tc1 n2 tc2 e_n1_n2 : unit =
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
          (fun u1 u2 -> Solver.cc_merge_t solver u1 u2 expl)
          l1 l2
      ) else (
        (* different function: disjointness *)
        Solver.raise_conflict solver expl
      )
    | _ -> assert false

  (* attach data to constructor terms *)
  let on_new_term _ n (t:T.t) =
    match A.view_as_cstor t with
    | T_cstor _ -> Some {t;n}
    | _ -> None

  let create_and_setup (solver:Solver.t) : t =
    let k = Solver.Key.create solver ~on_merge (module Data) in
    Solver.on_cc_merge solver ~k on_merge;
    Solver.on_cc_new_term solver ~k on_new_term;
    {k}

  let theory = A.S.mk_theory ~name ~create_and_setup ()
end
