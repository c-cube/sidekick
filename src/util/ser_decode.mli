(** Decoders for {!Ser_value}.

    Combinators to decode values. *)

type +'a t
(** Decode a value of type ['a] *)

val int : int t
val bool : bool t
val string : string t
val return : 'a -> 'a t
val fail : string -> 'a t
val unwrap_opt : string -> 'a option -> 'a t
(** Unwrap option, or fail *)
val any : Ser_value.t t
val list : 'a t -> 'a list t
val dict_field : string -> 'a t -> 'a t
val dict_field_opt : string -> 'a t -> 'a option t
val both : 'a t -> 'b t -> ('a * 'b) t
val try_l : 'a t list -> 'a t

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

module Error : sig
  type t

  include Sidekick_sigs.PRINT with type t := t

  val to_string : t -> string
end

val run : 'a t -> Ser_value.t -> ('a, Error.t) result

val run_exn : 'a t -> Ser_value.t -> 'a
(** @raise Error.Error in case of failure *)
