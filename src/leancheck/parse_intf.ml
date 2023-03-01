module type CALLBACK = sig
  val ns : int -> string -> unit
  val ni : int -> int -> unit
end
