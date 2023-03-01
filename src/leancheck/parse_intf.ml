module type CALLBACK = sig
  val line : string -> unit
  val ns : int -> string -> unit
  val ni : int -> int -> unit
end
