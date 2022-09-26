(** Constants.

  Constants are logical symbols, defined by the user thanks to an open type *)

open Types_

type view = const_view = ..

module Ops : sig
  type t = const_ops = {
    pp: const_view Fmt.printer;  (** Pretty-print constant *)
    equal: const_view -> const_view -> bool;
        (** Equality of constant with any other constant *)
    hash: const_view -> int;  (** Hash constant *)
    ser: (term -> Ser_value.t) -> const_view -> string * Ser_value.t;
        (** Serialize a constant, along with a tag to recognize it. *)
  }
end

type t = const = { c_view: view; c_ops: Ops.t; c_ty: term }

val view : t -> view
val make : view -> Ops.t -> ty:term -> t
val ser : ser_t:(term -> Ser_value.t) -> t -> string * Ser_value.t
val ty : t -> term

type decoders =
  (string * Ops.t * (term Ser_decode.t -> view Ser_decode.t)) list
(** Decoders for constants: given a term store, return a list
    of supported tags, and for each tag, a decoder for constants
    that have this particular tag. *)

include EQ_HASH_PRINT with type t := t
