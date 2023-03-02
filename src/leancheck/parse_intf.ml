module type CALLBACK = sig
  val line : string -> unit
  val ns : at:int -> int -> string -> unit
  val ni : at:int -> int -> int -> unit
  val us : at:int -> int -> unit
  val um : at:int -> int -> int -> unit
  val uim : at:int -> int -> int -> unit
  val up : at:int -> int -> unit
end
