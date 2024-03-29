open Sidekick_core

type t = {
  tst: Term.store;
  proof: Sidekick_proof.Tracer.t;
  mutable hooks: hook list;
  (* store [t --> u by step_ids] in the cache.
     We use a bag for the proof steps because it gives us structural
     sharing of subproofs. *)
  cache: (Term.t * Sidekick_proof.Step.id Bag.t) Term.Tbl.t;
}

and hook = t -> Term.t -> (Term.t * Sidekick_proof.Step.id Iter.t) option

let create tst ~proof : t =
  let proof = (proof : #Sidekick_proof.Tracer.t :> Sidekick_proof.Tracer.t) in
  { tst; proof; hooks = []; cache = Term.Tbl.create 32 }

let[@inline] tst self = self.tst
let[@inline] proof self = self.proof
let add_hook self f = self.hooks <- f :: self.hooks
let clear self = Term.Tbl.clear self.cache

let normalize (self : t) (t : Term.t) : (Term.t * Sidekick_proof.Step.id) option
    =
  (* compute and cache normal form of [t] *)
  let rec loop t : Term.t * _ Bag.t =
    match Term.Tbl.find self.cache t with
    | res -> res
    | exception Not_found ->
      if Term.is_a_type t then
        t, Bag.empty
      else (
        let steps_u = ref Bag.empty in
        let u = aux_rec ~steps:steps_u t self.hooks in
        Term.Tbl.add self.cache t (u, !steps_u);
        u, !steps_u
      )
  and loop_add ~steps t =
    let u, pr_u = loop t in
    steps := Bag.append !steps pr_u;
    u
  (* try each function in [hooks] successively, and rewrite subterms *)
  and aux_rec ~steps t hooks : Term.t =
    match hooks with
    | [] ->
      let u =
        Term.map_shallow self.tst t ~f:(fun _inb sub_t -> loop_add ~steps sub_t)
      in
      if Term.equal t u then
        t
      else
        loop_add ~steps u
    | h :: hooks_tl ->
      (match h self t with
      | None -> aux_rec ~steps t hooks_tl
      | Some (u, _) when Term.equal t u -> aux_rec ~steps t hooks_tl
      | Some (u, pr_u) ->
        let bag_u = Bag.of_iter pr_u in
        steps := Bag.append !steps bag_u;
        let v, pr_v = loop u in
        (* fixpoint *)
        steps := Bag.append !steps pr_v;
        v)
  in
  let u, pr_u = loop t in
  if Term.equal t u then
    None
  else (
    (* proof: [sub_proofs |- t=u] by CC + subproof *)
    let step =
      Sidekick_proof.Tracer.add_step self.proof @@ fun () ->
      Sidekick_proof.Core_rules.lemma_preprocess t u ~using:(Bag.to_list pr_u)
    in
    Some (u, step)
  )

let normalize_t self t =
  match normalize self t with
  | Some (u, pr_u) -> u, Some pr_u
  | None -> t, None
