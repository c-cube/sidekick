
(** {1 Types used by the congruence closure} *)

type ('f, 't, 'ts) view =
  | Bool of bool
  | App_fun of 'f * 'ts
  | App_ho of 't * 'ts
  | If of 't * 't * 't
  | Eq of 't * 't
  | Opaque of 't (* do not enter *)

let[@inline] map_view ~f_f ~f_t ~f_ts (v:_ view) : _ view =
  match v with
  | Bool b -> Bool b
  | App_fun (f, args) -> App_fun (f_f f, f_ts args)
  | App_ho (f, args) -> App_ho (f_t f, f_ts args)
  | If (a,b,c) -> If (f_t a, f_t b, f_t c)
  | Eq (a,b) -> Eq (f_t a, f_t b)
  | Opaque t -> Opaque (f_t t)

let iter_view ~f_f ~f_t ~f_ts (v:_ view) : unit =
  match v with
  | Bool _ -> ()
  | App_fun (f, args) -> f_f f; f_ts args
  | App_ho (f, args) -> f_t f; f_ts args
  | If (a,b,c) -> f_t a; f_t b; f_t c;
  | Eq (a,b) -> f_t a; f_t b
  | Opaque t -> f_t t

module type TERM = sig
  module Fun : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
  end

  module Term : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    type state

    val bool : state -> bool -> t

    (** View the term through the lens of the congruence closure *)
    val cc_view : t -> (Fun.t, t, t Sequence.t) view
  end
end

module type TERM_LIT = sig
  include TERM

  module Lit : sig
    type t
    val neg : t -> t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    val sign : t -> bool
    val term : t -> Term.t
  end
end

module type FULL = sig
  include TERM_LIT

  module Proof : sig
    type t
    val pp : t Fmt.printer

    val default : t
    (* TODO: to give more details
    val cc_lemma : unit -> t
       *)
  end

  module Ty : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
  end

  module Value : sig
    type t

    val pp : t Fmt.printer

    val fresh : Term.t -> t

    val true_ : t
    val false_ : t
  end

  module Model : sig
    type t

    val pp : t Fmt.printer

    val eval : t -> Term.t -> Value.t option
    (** Evaluate the term in the current model *)

    val add : Term.t -> Value.t -> t -> t
  end
end

(* TODO: micro theory *)
