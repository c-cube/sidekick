(** Decoders for {!Ser_value}.

    Combinators to decode values. *)

(** Errors *)
module Error : sig
  type t

  include Sidekick_sigs.PRINT with type t := t

  val to_string : t -> string
  val of_string : string -> Ser_value.t -> t
end

(** {2 Main combinators *)

type +'a t
(** Decode a value of type ['a] *)

val int : int t
val bool : bool t
val string : string t
val return : 'a -> 'a t
val return_result : ('a, string) result -> 'a t
val return_result_err : ('a, Error.t) result -> 'a t
val delay : (unit -> 'a t) -> 'a t
val fail : string -> 'a t
val failf : ('a, Format.formatter, unit, 'b t) format4 -> 'a
val fail_err : Error.t -> 'a t

val unwrap_opt : string -> 'a option -> 'a t
(** Unwrap option, or fail *)

val any : Ser_value.t t
val list : 'a t -> 'a list t
val tup2 : 'a t -> 'b t -> ('a * 'b) t
val tup3 : 'a t -> 'b t -> 'c t -> ('a * 'b * 'c) t
val tup4 : 'a t -> 'b t -> 'c t -> 'd t -> ('a * 'b * 'c * 'd) t
val dict_field : string -> 'a t -> 'a t
val dict_field_opt : string -> 'a t -> 'a option t
val dict_field_or : 'a -> string -> 'a t -> 'a t
val both : 'a t -> 'b t -> ('a * 'b) t

val reflect : 'a t -> Ser_value.t -> ('a, Error.t) result t
(** [reflect dec v] returns the result of decoding [v] with [dec] *)

val reflect_or_fail : 'a t -> Ser_value.t -> 'a t

val try_l : 'a t list -> 'a t
(** [try_l fs] tries each [f in fs] turn by turn, until one succeeds *)

module Infix : sig
  val ( >|= ) : 'a t -> ('a -> 'b) -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
end

include module type of Infix

(** {2 Deserializing} *)

val run : 'a t -> Ser_value.t -> ('a, Error.t) result

val run_exn : 'a t -> Ser_value.t -> 'a
(** @raise Error.Error in case of failure *)
