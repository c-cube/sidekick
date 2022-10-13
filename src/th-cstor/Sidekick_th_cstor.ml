open Sidekick_core
module Proof = Sidekick_proof
module SMT = Sidekick_smt_solver
module SI = SMT.Solver_internal
module T = Term

type ('c, 't) cstor_view = T_cstor of 'c * 't array | T_other of 't

let name = "th-cstor"

module type ARG = sig
  val view_as_cstor : Term.t -> (Const.t, Term.t) cstor_view
  val lemma_cstor : Lit.t list -> Proof.Pterm.t
end

module Make (A : ARG) : sig
  val theory : SMT.theory
end = struct
  open Sidekick_cc

  module Monoid = struct
    (* associate to each class a unique constructor term in the class (if any) *)
    type t = { t: T.t; n: E_node.t; cstor: Const.t; args: E_node.t array }

    let name = name

    type state = { n_merges: int Stat.counter; n_conflict: int Stat.counter }

    let create cc : state =
      {
        n_merges = Stat.mk_int (CC.stat cc) "th.cstor.merges";
        n_conflict = Stat.mk_int (CC.stat cc) "th.cstor.conflicts";
      }

    let pp out (v : t) =
      Fmt.fprintf out "(@[cstor %a@ :term %a@])" Const.pp v.cstor T.pp_debug v.t

    (* attach data to constructor terms *)
    let of_term cc _ n (t : T.t) : _ option * _ =
      match A.view_as_cstor t with
      | T_cstor (cstor, args) ->
        let args = CCArray.map (CC.add_term cc) args in
        Some { n; t; cstor; args }, []
      | _ -> None, []

    let merge _cc state n1 v1 n2 v2 e_n1_n2 : _ result =
      Log.debugf 5 (fun k ->
          k "(@[%s.merge@ @[:c1 %a (t %a)@]@ @[:c2 %a (t %a)@]@])" name
            E_node.pp n1 T.pp_debug v1.t E_node.pp n2 T.pp_debug v2.t);
      (* build full explanation of why the constructor terms are equal *)
      (* FIXME: add a (fun p -> A.lemma_cstor p …) here.
         probably we need [Some a=Some b => a=b] as a lemma for inj,
         and [Some a /= None] for Error case. *)
      let expl =
        Expl.mk_list [ e_n1_n2; Expl.mk_merge n1 v1.n; Expl.mk_merge n2 v2.n ]
      in
      if Const.equal v1.cstor v2.cstor then (
        (* same function: injectivity *)
        assert (CCArray.length v1.args = CCArray.length v2.args);
        let acts =
          CCArray.map2
            (fun u1 u2 ->
              Stat.incr state.n_merges;
              CC.Handler_action.Act_merge (u1, u2, expl))
            v1.args v2.args
          |> Array.to_list
        in
        Ok (v1, acts)
      ) else (
        (* different function: disjointness *)
        Stat.incr state.n_conflict;
        Error (CC.Handler_action.Conflict expl)
      )
  end

  module ST = Sidekick_cc.Plugin.Make (Monoid)

  type t = ST.t

  let push_level ((module P) : t) = P.push_level ()
  let pop_levels ((module P) : t) n = P.pop_levels n
  let n_levels ((module P) : t) = P.n_levels ()

  let create_and_setup ~id:_ (si : SI.t) : t =
    Log.debug 1 "(setup :th-cstor)";
    let self = ST.create_and_setup ~size:32 (SI.cc si) in
    self

  let theory =
    SMT.Solver.mk_theory ~name ~push_level ~pop_levels ~create_and_setup ()
end

let make (module A : ARG) : SMT.theory =
  let module M = Make (A) in
  M.theory
