type t = private int

include Sidekick_sigs.PRINT with type t := t

(**/*)
module Internal_ : sig
  val make : int -> t
end
(**/*)
