(** Entry in the sink.

   This integer tag represent a single entry in a trace, for example
   a line if we serialized using line-separate json values.
   In general each entry has its own unique ID that is monotonically
   increasing with time. *)

include Int_id.Make ()
