(** Proof trace with serialization

    This library is useful to serialize a series of reasoning steps
    in memory or into a file, to be able to reconstruct a proper
    proof later. *)

module Proof_ser = Proof_ser
module Storage = Storage

let iter_steps_backward = Storage.iter_steps_backward
