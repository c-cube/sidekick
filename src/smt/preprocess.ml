open Sigs

module type PREPROCESS_ACTS = sig
  val proof : proof_trace
  val mk_lit : ?sign:bool -> term -> lit
  val add_clause : lit list -> step_id -> unit
  val add_lit : ?default_pol:bool -> lit -> unit
end

type preprocess_actions = (module PREPROCESS_ACTS)

(* action taken later *)
type delayed_action =
  | DA_add_clause of lit list * step_id
  | DA_add_lit of { default_pol: bool option; lit: lit }

type t = {
  tst: Term.store;  (** state for managing terms *)
  proof: proof_trace;
  mutable preprocess: preprocess_hook list;
  preprocessed: Term.t Term.Tbl.t;
  delayed_actions: delayed_action Vec.t;
  n_preprocess_clause: int Stat.counter;
}

and preprocess_hook = t -> preprocess_actions -> term -> term option

let create ?(stat = Stat.global) ~proof tst : t =
  {
    tst;
    proof;
    preprocess = [];
    preprocessed = Term.Tbl.create 8;
    delayed_actions = Vec.create ();
    n_preprocess_clause = Stat.mk_int stat "smt.preprocess.n-clauses";
  }

let on_preprocess self f = self.preprocess <- f :: self.preprocess

let preprocess_term_ (self : t) (t0 : term) : unit =
  let module A = struct
    let proof = self.proof
    let mk_lit ?sign t : Lit.t = Lit.atom ?sign self.tst t

    let add_lit ?default_pol lit : unit =
      Vec.push self.delayed_actions (DA_add_lit { default_pol; lit })

    let add_clause c pr : unit =
      Vec.push self.delayed_actions (DA_add_clause (c, pr))
  end in
  let acts = (module A : PREPROCESS_ACTS) in

  (* how to preprocess a term and its subterms *)
  let rec preproc_rec_ t : Term.t =
    match Term.Tbl.find_opt self.preprocessed t with
    | Some u -> u
    | None ->

      (* process sub-terms first *)
      let u = Term.map_shallow self.tst t
        ~f:(fun _inb u -> preproc_rec_ u);

      Log.debugf 50 (fun k -> k "(@[smt.preprocess@ %a@])" Term.pp_debug t);

      (* signal boolean subterms, so as to decide them
         in the SAT solver *)
      if Ty.is_bool (Term.ty t) then (
        Log.debugf 5 (fun k ->
            k "(@[solver.map-bool-subterm-to-lit@ :subterm %a@])" Term.pp_debug
              t);

        (* make a literal *)
        let lit = Lit.atom self.tst t in
        (* ensure that SAT solver has a boolean atom for [u] *)
        delayed_add_lit self lit;

        (* also map [sub] to this atom in the congruence closure, for propagation *)
        let cc = cc self in
        CC.set_as_lit cc (CC.add_term cc t) lit;


        Term.Tbl.add self.preprocessed t u;
      )

      List.iter (fun f -> f self acts t) self.preprocess
    )
  in
  preproc_rec_ t0
