(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

module type S = sig
  type st

  type clause
  (** The type of clauses *)

  val export :
    st ->
    Format.formatter ->
    clauses:clause Vec.t ->
    unit
end

module Make(St : Sidekick_sat.S) = struct
  type st = St.t

  (* Dimacs & iCNF export *)
  let export_vec name fmt vec =
    Format.fprintf fmt "c %s@,%a@," name (Vec.print ~sep:"" St.Clause.pp_dimacs) vec

  let export_assumption fmt vec =
    Format.fprintf fmt "c Local assumptions@,a %a@," St.Clause.pp_dimacs vec

  let map_filter_learnt c =
    match St.Clause.premise c with
    | St.Hyp -> assert false
    | St.Lemma _ -> Some c
    | St.History l ->
      begin match l with
        | [] -> assert false
        | d :: _ ->
          begin match St.Clause.premise d with
            | St.Lemma _ -> Some d
            | St.Hyp | St.History _ -> None
          end
      end

  let filter_vec learnt =
    let lemmas = Vec.make (Vec.size learnt) St.Clause.dummy in
    Vec.iter (fun c ->
        match map_filter_learnt c with
        | None -> ()
        | Some d -> Vec.push lemmas d
      ) learnt;
    lemmas

  let export st fmt ~clauses : unit =
    (* Number of atoms and clauses *)
    let n = St.n_vars st in
    let m = Vec.size clauses in
    Format.fprintf fmt
      "@[<v>p cnf %d %d@,%a@]@." n m
      (export_vec "Clauses") clauses
end

