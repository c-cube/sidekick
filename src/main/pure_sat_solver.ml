(* pure SAT solver *)

open Sidekick_core
module E = CCResult
module SS = Sidekick_sat

(* FIXME
   (* TODO: on the fly compression *)
   module Proof : sig
     include module type of struct
       include Proof_trace
     end

     type in_memory

     val create_in_memory : unit -> t * in_memory
     val to_string : in_memory -> string
     val to_chan : out_channel -> in_memory -> unit
     val create_to_file : string -> t
     val close : t -> unit

     type event = Sidekick_bin_lib.Drup_parser.event =
       | Input of int list
       | Add of int list
       | Delete of int list

     val iter_events : in_memory -> event Iter.t
   end = struct
     include Proof_trace
     module PT = Proof_term

     let bpf = Printf.bprintf
     let fpf = Printf.fprintf

     type lit = Lit.t
     type in_memory = Buffer.t

     let to_string = Buffer.contents

     (*
     type t =
       | Dummy
       | Inner of in_memory
       | Out of { oc: out_channel; close: unit -> unit }
       *)

     let[@inline] emit_lits_buf_ buf lits = lits (fun i -> bpf buf "%d " i)
     let[@inline] emit_lits_out_ oc lits = lits (fun i -> fpf oc "%d " i)

     let create_in_memory () =
       let buf = Buffer.create 1_024 in
       let pr =
         (module struct
           let enabled () = true
           let add_step s = assert false

           (* TODO: helper to flatten?
              let pt : PT.t = s () in
               match pt.
           *)

           (* TODO *)
           let add_unsat _ = ()

           (* TODO *)
           let delete _ = ()
         end : DYN)
       in
       pr, buf

     (*
     module Rule = struct
       type nonrec lit = lit
       type nonrec rule = rule
       type nonrec step_id = step_id

       let sat_input_clause lits self =
         match self with
         | Dummy -> ()
         | Inner buf ->
           bpf buf "i ";
           emit_lits_buf_ buf lits;
           bpf buf "0\n"
         | Out { oc; _ } ->
           fpf oc "i ";
           emit_lits_out_ oc lits;
           fpf oc "0\n"

       let sat_redundant_clause lits ~hyps:_ self =
         match self with
         | Dummy -> ()
         | Inner buf ->
           bpf buf "r ";
           emit_lits_buf_ buf lits;
           bpf buf "0\n"
         | Out { oc; _ } ->
           fpf oc "r ";
           emit_lits_out_ oc lits;
           fpf oc "0\n"

       let sat_unsat_core _ _ = ()
     end

     let del_clause () lits self =
       match self with
       | Dummy -> ()
       | Inner buf ->
         bpf buf "d ";
         emit_lits_buf_ buf lits;
         bpf buf "0\n"
       | Out { oc; _ } ->
         fpf oc "d ";
         emit_lits_out_ oc lits;
         fpf oc "0\n"


     let create_in_memory () : t * in_memory =
       let buf = Buffer.create 1_024 in
       Inner buf, buf

     let create_to_file file =
       let oc, close =
         match Filename.extension file with
         | ".gz" ->
           let cmd = Printf.sprintf "gzip -c - > \"%s\"" (String.escaped file) in
           Log.debugf 1 (fun k -> k "proof file: command is %s" cmd);
           let oc = Unix.open_process_out cmd in
           oc, fun () -> ignore (Unix.close_process_out oc : Unix.process_status)
         | ".drup" ->
           let oc = open_out_bin file in
           oc, fun () -> close_out_noerr oc
         | s -> Error.errorf "unknown file extension '%s'" s
       in
       Out { oc; close }

     let close = function
       | Dummy | Inner _ -> ()
       | Out { close; oc } ->
         flush oc;
         close ()

     let to_string = Buffer.contents
     let to_chan = Buffer.output_buffer

     module DP = Sidekick_bin_lib.Drup_parser

     type event = DP.event =
       | Input of int list
       | Add of int list
       | Delete of int list

     (* parse the proof back *)
     let iter_events (self : in_memory) : DP.event Iter.t =
       let dp = DP.create_string (to_string self) in
       DP.iter dp

       *)
   end
*)

module I_const : sig
  val make : Term.store -> int -> Lit.t
end = struct
  type Const.view += I of int

  let ops =
    (module struct
      let equal a b =
        match a, b with
        | I a, I b -> a = b
        | _ -> false

      let hash = function
        | I i -> Hash.int i
        | _ -> assert false

      let pp out = function
        | I i -> Fmt.int out i
        | _ -> assert false
    end : Const.DYN_OPS)

  let make tst i : Lit.t =
    let t = Term.const tst @@ Const.make (I (abs i)) ops ~ty:(Term.bool tst) in
    Lit.atom ~sign:(i > 0) tst t
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
