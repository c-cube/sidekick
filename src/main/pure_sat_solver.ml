
(* pure SAT solver *)

module E = CCResult
module SS = Sidekick_sat

module Formula = struct
  type t = int
  let norm t = if t>0 then t, SS.Same_sign else -t, SS.Negated
  let abs = abs
  let sign t = t>0
  let equal = CCInt.equal
  let hash = CCHash.int
  let neg x = -x
  let pp = Fmt.int
end

(* TODO: on the fly compression *)
module Proof : sig
  include Sidekick_sat.PROOF with type lit = Formula.t

  val dummy : t
  val create : unit -> t
  val to_string : t -> string
  val to_chan : out_channel -> t -> unit
  type event = Sidekick_bin_lib.Drup_parser.event =
    | Input of int list
    | Add of int list
    | Delete of int list
  val iter_events : t -> event Iter.t
end = struct
  let bpf = Printf.bprintf
  type lit = Formula.t
  type t =
    | Dummy
    | Inner of {
        buf: Buffer.t;
      }
  type dproof = t -> unit

  let[@inline] enabled = function
    | Dummy -> false
    | Inner _ -> true

  let emit_lits_ buf lits =
    lits (fun i -> bpf buf "%d " i)

  let emit_input_clause self lits =
    match self with
    | Dummy -> ()
    | Inner {buf} ->
      bpf buf "i "; emit_lits_ buf lits; bpf buf "0\n"

  let emit_redundant_clause self lits =
    match self with
    | Dummy -> ()
    | Inner {buf} ->
      bpf buf "r "; emit_lits_ buf lits; bpf buf "0\n"

  let del_clause self lits =
    match self with
    | Dummy -> ()
    | Inner {buf} ->
      bpf buf "d "; emit_lits_ buf lits; bpf buf "0\n"

  (* lifetime *)

  let dummy : t = Dummy
  let create () : t = Inner {buf=Buffer.create 1_024}

  let to_string = function
    | Dummy -> ""
    | Inner {buf} -> Buffer.contents buf

  let to_chan oc = function
    | Dummy -> ()
    | Inner {buf} -> Buffer.output_buffer oc buf; flush oc

  module DP = Sidekick_bin_lib.Drup_parser

  type event = DP.event =
    | Input of int list
    | Add of int list
    | Delete of int list

  (* parse the proof back *)
  let iter_events (self:t) : DP.event Iter.t =
    match self with
    | Dummy -> Iter.empty
    | Inner {buf} ->
      let dp = DP.create_string (to_string self) in
      DP.iter dp
end

module Arg = struct
  module Formula = Formula
  type formula = Formula.t
  module Proof = Proof
  type proof = Proof.t
end

module SAT = Sidekick_sat.Make_pure_sat(Arg)

module Dimacs = struct
  open Sidekick_base
  module BL = Sidekick_bin_lib
  module T = Term

  let parse_file (solver:SAT.t) (file:string) : (unit, string) result =
    let get_lit i : SAT.atom = SAT.make_atom solver i in

    try
      CCIO.with_in file
        (fun ic ->
           let p = BL.Dimacs_parser.create ic in
           BL.Dimacs_parser.iter p
             (fun c ->
                let atoms = List.rev_map get_lit c in
                SAT.add_input_clause solver atoms);
           Ok ())
    with e ->
      E.of_exn_trace e
end

let check_proof proof : bool =
  Profile.with_ "pure-sat.check-proof" @@ fun () ->
  let module SDRUP = Sidekick_drup.Make() in
  let store = SDRUP.Clause.create() in
  let checker = SDRUP.Checker.create store in
  let ok = ref true in

  let tr_clause c =
    let c = List.rev_map SDRUP.Atom.of_int_dimacs c in
    SDRUP.Clause.of_list store c
  in

  Proof.iter_events proof
    (function
      | Proof.Input c ->
        let c = tr_clause c in
        SDRUP.Checker.add_clause checker c

      | Proof.Add c ->
        let c = tr_clause c in
        if not (SDRUP.Checker.is_valid_drup checker c) then (
          ok := false;
        );
        SDRUP.Checker.add_clause checker c;

      | Proof.Delete c ->
        let c = tr_clause c in
        SDRUP.Checker.del_clause checker c;
    );
  !ok

let solve ?(check=false) (solver:SAT.t) : (unit, string) result =
  let res =
    Profile.with_ "solve" (fun () -> SAT.solve solver)
  in
  let t2 = Sys.time () in
  Printf.printf "\r"; flush stdout;
  begin match res with
    | SAT.Sat _ ->
      let t3 = Sys.time () -. t2 in
      Format.printf "Sat (%.3f/%.3f)@." t2 t3;
    | SAT.Unsat (module US) ->

      if check then (
        let proof = SAT.proof solver in
        let ok = check_proof proof in
        if not ok then (
          Error.errorf "Proof validation failed"
        );
      );

      let t3 = Sys.time () -. t2 in
      Format.printf "Unsat (%.3f/%.3f)@." t2 t3;
  end;
  Ok ()

