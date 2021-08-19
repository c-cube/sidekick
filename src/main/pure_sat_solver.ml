
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

module Proof
  : Sidekick_sat.PROOF with type lit = Formula.t
= struct
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
        Proof.check proof;
      );

      let t3 = Sys.time () -. t2 in
      Format.printf "Unsat (%.3f/%.3f)@." t2 t3;
  end;
  Ok ()

