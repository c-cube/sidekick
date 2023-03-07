module type CALLBACK = sig
  val line : string -> unit
  val after_line : unit -> unit
  val ns : at:int -> int -> string -> unit
  val ni : at:int -> int -> int -> unit
  val us : at:int -> int -> unit
  val um : at:int -> int -> int -> unit
  val uim : at:int -> int -> int -> unit
  val up : at:int -> int -> unit
  val ev : at:int -> int -> unit
  val ea : at:int -> int -> int -> unit
  val ec : at:int -> int -> int list -> unit
  val es : at:int -> int -> unit
  val el : at:int -> string -> int -> int -> int -> unit
  val ep : at:int -> string -> int -> int -> int -> unit

  val ind :
    n_params:int ->
    nidx:int ->
    tyidx:int ->
    intros:(int * int) list ->
    univ_params:int list ->
    unit
end
