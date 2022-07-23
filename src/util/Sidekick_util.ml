(* re-exports *)
module Fmt = CCFormat
module Util = Util
module Vec = Vec
module Veci = Veci
module Vec_float = Vec_float
module Vec_unit = Vec_unit
module Vec_sig = Vec_sig
module Bitvec = Bitvec
module Int_id = Int_id

(* TODO: a specialized representation *)
module Int_tbl = Util.Int_tbl
module Int_set = Util.Int_set
module Int_map = Util.Int_map
module Event = Event
module Backtrack_stack = Backtrack_stack
module Backtrackable_tbl = Backtrackable_tbl
module Backtrackable_ref = Backtrackable_ref
module Log = Log
module Error = Error
module Bag = Bag
module Stat = Stat
module Hash = Hash
module Profile = Profile
module Chunk_stack = Chunk_stack

let[@inline] ( let@ ) f x = f x
