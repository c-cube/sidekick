(* pure SAT solver *)

open Sidekick_core
module Tracer = Sidekick_smt_solver.Tracer
module E = CCResult
module SS = Sidekick_sat

module I_const : sig
  val make : Term.store -> int -> Lit.t
  val const_decoders : Const.decoders
end = struct
  type Const.view += I of int

  let ops =
    let equal a b =
      match a, b with
      | I a, I b -> a = b
      | _ -> false
    in

    let hash = function
      | I i -> Hash.int i
      | _ -> assert false
    in

    let pp out = function
      | I i -> Fmt.int out i
      | _ -> assert false
    in

    let ser _sink = function
      | I i -> "sat.lit", Ser_value.(int i)
      | _ -> assert false
    in
    { Const.Ops.equal; hash; pp; ser }

  let const_decoders : Const.decoders =
    [
      ( "sat.lit",
        ops,
        Ser_decode.(
          fun _tst ->
            let+ i = int in
            I i) );
    ]

  let make tst i : Lit.t =
    let t = Term.const tst @@ Const.make (I (abs i)) ops ~ty:(Term.bool tst) in
    Lit.atom ~sign:(i > 0) tst t

  let deser _tst =
    Ser_decode.(
      ( "sat.lit",
        [
          (let+ i = int in
           I i);
        ] ))
end

module SAT = Sidekick_sat

module Dimacs = struct
  open Sidekick_base
  module BL = Sidekick_bin_lib
  module T = Term

  let parse_file (solver : SAT.t) (tst : Term.store) (file : string) :
      (unit, string) result =
    try
      CCIO.with_in file (fun ic ->
          let p = BL.Dimacs_parser.create ic in
          BL.Dimacs_parser.iter p (fun c ->
              (* convert on the fly *)
              let c = List.map (I_const.make tst) c in
              SAT.add_input_clause solver c);
          Ok ())
    with e -> E.of_exn_trace e
end

(* FIXME
   let check_proof (proof : Proof.in_memory) : bool =
     Profile.with_ "pure-sat.check-proof" @@ fun () ->
     let module SDRUP = Sidekick_drup.Make () in
     let store = SDRUP.Clause.create () in
     let checker = SDRUP.Checker.create store in
     let ok = ref true in

     let tr_clause c =
       let c = List.rev_map SDRUP.Atom.of_int_dimacs c in
       SDRUP.Clause.of_list store c
     in

     Proof.iter_events proof (function
       | Proof.Input c ->
         let c = tr_clause c in
         SDRUP.Checker.add_clause checker c
       | Proof.Add c ->
         let c = tr_clause c in
         if not (SDRUP.Checker.is_valid_drup checker c) then ok := false;
         SDRUP.Checker.add_clause checker c
       | Proof.Delete c ->
         let c = tr_clause c in
         SDRUP.Checker.del_clause checker c);
     !ok
*)

let start = Sys.time ()

let solve ?(check = false) ?in_memory_proof (solver : SAT.t) :
    (unit, string) result =
  let res = Profile.with_ "solve" (fun () -> SAT.solve solver) in
  let t2 = Sys.time () in
  Printf.printf "\r";
  flush stdout;
  (match res with
  | SAT.Sat _ ->
    let t3 = Sys.time () in
    Format.printf "Sat (%.3f/%.3f)@." (t2 -. start) (t3 -. t2)
  | SAT.Unsat _ ->
    if check then (
      match in_memory_proof with
      | None ->
        Error.errorf "Cannot validate proof, no in-memory proof provided"
      | Some _proof ->
        let ok = true (* FIXME check_proof proof *) in
        if not ok then Error.errorf "Proof validation failed"
    );

    let t3 = Sys.time () in
    Format.printf "Unsat (%.3f/%.3f)@." (t2 -. start) (t3 -. t2));
  Ok ()
