module type CALLBACK = sig
  val line : string -> unit
  val ns : at:int -> int -> string -> unit
  val ni : at:int -> int -> int -> unit
end
