(** Abstract interface for a solver *)

module Unknown = Unknown
module Check_res = Check_res
module Asolver = Asolver

class type t = Asolver.t
(** Main abstract solver type *)
