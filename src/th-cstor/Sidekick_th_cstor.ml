(** {1 Theory for constructors} *)

type ('c,'t) cstor_view =
  | T_cstor of 'c * 't IArray.t
  | T_other of 't

let name = "th-cstor"

module type ARG = sig
  module S : Sidekick_core.SOLVER
  val view_as_cstor : S.T.Term.t -> (S.T.Fun.t, S.T.Term.t) cstor_view
  val lemma_cstor : S.proof -> S.Lit.t Iter.t -> unit
end

module type S = sig
  module A : ARG
  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module SI = A.S.Solver_internal
  module T = A.S.T.Term
  module N = SI.CC.N
  module Fun = A.S.T.Fun
  module Expl = SI.CC.Expl

  module Monoid = struct
    module SI = SI

    (* associate to each class a unique constructor term in the class (if any) *)
    type t = {
      t: T.t;
      n: N.t;
      cstor: Fun.t;
      args: N.t IArray.t;
    }

    let name = name
    let pp out (v:t) =
      Fmt.fprintf out "(@[cstor %a@ :term %a@])" Fun.pp v.cstor T.pp v.t

    (* attach data to constructor terms *)
    let of_term cc n (t:T.t) : _ option * _ =
      match A.view_as_cstor t with
      | T_cstor (cstor,args) ->
        let args = IArray.map (SI.CC.add_term cc) args in
        Some {n; t; cstor; args}, []
      | _ -> None, []

    let merge cc n1 v1 n2 v2 e_n1_n2 : _ result =
      Log.debugf 5
        (fun k->k "(@[%s.merge@ @[:c1 %a (t %a)@]@ @[:c2 %a (t %a)@]@])"
            name N.pp n1 T.pp v1.t N.pp n2 T.pp v2.t);
      (* build full explanation of why the constructor terms are equal *)
      (* FIXME: add a (fun p -> A.lemma_cstor p …) here.
         probably we need [Some a=Some b => a=b] as a lemma for inj,
         and [Some a /= None] for Error case. *)
      let expl =
        Expl.mk_list [
          e_n1_n2;
          Expl.mk_merge n1 v1.n;
          Expl.mk_merge n2 v2.n;
        ]
      in
      if Fun.equal v1.cstor v2.cstor then (
        (* same function: injectivity *)
        assert (IArray.length v1.args = IArray.length v2.args);
        IArray.iter2
          (fun u1 u2 -> SI.CC.merge cc u1 u2 expl)
          v1.args v2.args;
        Ok v1
      ) else (
        (* different function: disjointness *)
        Error expl
      )
  end

  module ST = Sidekick_core.Monoid_of_repr(Monoid)

  type t = ST.t

  let push_level = ST.push_level
  let pop_levels = ST.pop_levels

  let create_and_setup (solver:SI.t) : t =
    Log.debug 1 "(setup :th-cstor)";
    let self = ST.create_and_setup ~size:32 solver in
    self

  let theory =
    A.S.mk_theory ~name ~push_level ~pop_levels ~create_and_setup ()
end
