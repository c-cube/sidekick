
module type NUM = sig
  type t

  val zero : t
  val one : t
  val minus_one : t

  val abs : t -> t
  val sign : t -> int

  val of_int : int -> t
  include Sidekick_sigs.EQ with type t := t
  include Sidekick_sigs.ORD with type t := t
  include Sidekick_sigs.HASH with type t := t
  include Sidekick_sigs.PRINT with type t := t

  val (+) : t -> t -> t
  val (-) : t -> t -> t
  val ( * ) : t -> t -> t
  val (~-) : t -> t

  val neg : t -> t
  val min : t -> t -> t
  val max : t -> t -> t

  val (=) : t -> t -> bool
  val (<>) : t -> t -> bool
  val (>) : t -> t -> bool
  val (>=) : t -> t -> bool
  val (<) : t -> t -> bool
  val (<=) : t -> t -> bool
end

module type INT = sig
  include NUM

  val succ : t -> t
  val pred : t -> t
  val gcd : t -> t -> t
end

module type RATIONAL = sig
  include NUM
  type bigint

  val (/) : t -> t -> t
  val num : t -> bigint
  val denum : t -> bigint

  val infinity : t
  (** +infinity *)

  val minus_infinity : t

  val of_bigint : bigint -> t

  val is_real : t -> bool
  (** A proper real, not nan/infinity *)

  val is_int : t -> bool
  (** Is this a proper integer? *)

  val as_int : t -> bigint option
  (** Convert to an integer if it's one, return [None] otherwise *)

  val floor : t -> bigint
  (** Integer equal or below *)

  val ceil : t -> bigint
  (** Integer equal or above *)

  val pp_approx : int -> Format.formatter -> t -> unit
  (** Pretty print rational with given amount of precision
      (for example as a floating point number) *)
end

module type INT_FULL = sig
  include INT

  val sqrt : t -> t

  val divexact : t -> t -> t

  val (/) : t -> t -> t

  val rem : t -> t -> t

  val probab_prime : t -> bool

  val pow : t -> int -> t
end
