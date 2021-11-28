type t =
  | No_store
  | In_memory of Chunk_stack.Buf.t
  | On_disk of string * out_channel

val pp : Format.formatter -> t -> unit

val iter_steps_backward : t -> Proof_ser.Step.t Iter.t
