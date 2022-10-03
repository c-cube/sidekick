(* pure SAT solver *)

open Sidekick_core
module E = CCResult
module SS = Sidekick_sat
module Tr = Sidekick_trace

module I_const : sig
  type Const.view += I of int

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

(** Tracer that emit list of integers. *)
let tracer ~(sink : Tr.Sink.t) () : Clause_tracer.t =
  object (self)
    method encode_lit (lit : Lit.t) =
      let sign = Lit.sign lit in
      let i =
        match Term.view (Lit.term lit) with
        | Term.E_const { Const.c_view = I_const.I i; _ } -> abs i
        | _ -> assert false
      in
      Ser_value.int
        (if sign then
          i
        else
          -i)

    method assert_clause ~id (lits : Lit.t Iter.t) =
      let v =
        Ser_value.(
          dict_of_list
            [
              "id", int id;
              "c", list (lits |> Iter.map self#encode_lit |> Iter.to_rev_list);
            ])
      in
      Tr.Sink.emit sink ~tag:"AssCSat" v

    method unsat_clause ~id =
      let v = Ser_value.(dict_of_list [ "id", int id ]) in
      Tr.Sink.emit sink ~tag:"UnsatC" v

    method delete_clause ~id _lits : unit =
      let v = Ser_value.(dict_of_list [ "id", int id ]) in
      ignore (Tr.Sink.emit sink ~tag:"DelCSat" v : Tr.Entry_id.t)
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
