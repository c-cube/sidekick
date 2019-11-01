(** {1 Theory for constructors} *)

type ('c,'t) cstor_view =
  | T_cstor of 'c * 't list
  | T_other of 't

let name = "th-cstor"

module type ARG = sig
  module S : Sidekick_core.SOLVER
  val view_as_cstor : S.T.Term.t -> (S.T.Fun.t, S.T.Term.t) cstor_view
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

  type cstor_repr = {
    t: T.t;
    n: N.t;
    cstor: Fun.t;
    args: T.t list;
  }
  (* associate to each class a unique constructor term in the class (if any) *)

  module N_tbl = Backtrackable_tbl.Make(N)

  type t = {
    cstors: cstor_repr N_tbl.t; (* repr -> cstor for the class *)
    (* TODO: also allocate a bit in CC to filter out quickly classes without cstors? *)
  }

  let push_level self = N_tbl.push_level self.cstors
  let pop_levels self n = N_tbl.pop_levels self.cstors n

  (* attach data to constructor terms *)
  let on_new_term self _solver n (t:T.t) =
    match A.view_as_cstor t with
    | T_cstor (cstor,args) ->
      N_tbl.add self.cstors n {n; t; cstor; args};
    | _ -> ()

  let on_pre_merge (self:t) cc acts n1 n2 e_n1_n2 : unit =
    begin match N_tbl.get self.cstors n1, N_tbl.get self.cstors n2 with
      | Some cr1, Some cr2 ->
        Log.debugf 5
          (fun k->k "(@[th-cstor.on_pre_merge@ @[:c1 %a@ (term %a)@]@ @[:c2 %a@ (term %a)@]@])"
              N.pp n1 T.pp cr1.t N.pp n2 T.pp cr2.t); 
        (* build full explanation of why the constructor terms are equal *)
        let expl =
          Expl.mk_list [
            e_n1_n2;
            Expl.mk_merge n1 cr1.n;
            Expl.mk_merge n2 cr2.n;
          ]
        in
        if Fun.equal cr1.cstor cr2.cstor then (
          (* same function: injectivity *)
          assert (List.length cr1.args = List.length cr2.args);
          List.iter2
            (fun u1 u2 -> SI.CC.merge_t cc u1 u2 expl)
            cr1.args cr2.args
        ) else (
          (* different function: disjointness *)
          SI.CC.raise_conflict_from_expl cc acts expl
      )
      | None, Some cr ->
        N_tbl.add self.cstors n1 cr
      | Some _, None -> () (* already there on the left *)
      | None, None -> ()
    end

  let create_and_setup (solver:SI.t) : t =
    let self = {
      cstors=N_tbl.create ~size:32 ();
    } in
    Log.debug 1 "(setup :th-cstor)";
    SI.on_cc_new_term solver (on_new_term self);
    SI.on_cc_pre_merge solver (on_pre_merge self);
    self

  let theory =
    A.S.mk_theory ~name ~push_level ~pop_levels ~create_and_setup ()
end
