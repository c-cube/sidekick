open Sidekick_core

type var = Base_types_.var
type atom = Base_types_.atom
type clause = Base_types_.clause

module CVec = Base_types_.CVec

type var_reason = Base_types_.var_reason =
  | Decision
  | Bcp of clause
  | Bcp_lazy of clause lazy_t

type t
type store = t

val create : ?size:[< `Big | `Small | `Tiny > `Big ] -> stat:Stat.t -> unit -> t
val iter_vars : t -> (var -> unit) -> unit

module Var : sig
  type t = var

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val to_int : t -> int
  val of_int_unsafe : int -> t
  val level : store -> var -> int
  val set_level : store -> var -> int -> unit
  val reason : store -> var -> var_reason option
  val set_reason : store -> var -> var_reason option -> unit
  val weight : store -> var -> float
  val set_weight : store -> var -> float -> unit
  val mark : store -> var -> unit
  val unmark : store -> var -> unit
  val marked : store -> var -> bool
  val set_default_pol : store -> var -> bool -> unit
  val default_pol : store -> var -> bool
  val set_last_pol : store -> var -> bool -> unit
  val last_pol : store -> var -> bool
  val heap_idx : store -> var -> int
  val set_heap_idx : store -> var -> int -> unit
end

module Atom : sig
  type t = atom

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val to_int : t -> int
  val of_int_unsafe : int -> t
  val neg : t -> t
  val sign : t -> bool
  val of_var : var -> t
  val var : t -> var
  val pa : var -> t
  val na : var -> t

  module AVec = Sidekick_sat__Base_types_.Atom0.AVec
  module ATbl = Sidekick_sat__Base_types_.Atom0.ATbl

  val lit : store -> atom -> Lit.t
  val mark : store -> atom -> unit
  val unmark : store -> atom -> unit
  val marked : store -> atom -> bool
  val watched : store -> atom -> CVec.t
  val is_true : store -> atom -> bool
  val set_is_true : store -> atom -> bool -> unit
  val is_false : store -> t -> bool
  val has_value : store -> atom -> bool
  val reason : store -> t -> var_reason option
  val level : store -> t -> int
  val marked_both : store -> atom -> bool
  val proof_lvl0 : store -> ATbl.key -> int32 option
  val set_proof_lvl0 : store -> ATbl.key -> int32 -> unit
  val pp : store -> Format.formatter -> atom -> unit
  val pp_a : store -> Format.formatter -> atom array -> unit
  val pp_sign : t -> string
  val debug_reason : 'a -> Format.formatter -> int * var_reason option -> unit
  val pp_level : store -> Format.formatter -> t -> unit
  val debug_value : store -> Format.formatter -> atom -> unit
  val debug : store -> Format.formatter -> t -> unit
  val debug_a : store -> Format.formatter -> t array -> unit
end

module Clause : sig
  type t = clause

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val to_int : t -> int
  val of_int_unsafe : int -> t

  module Tbl : Hashtbl.S with type key = t
  module CVec = Base_types_.CVec

  val make_a : store -> removable:bool -> atom array -> int32 -> t
  val make_l : store -> removable:bool -> atom list -> int32 -> t
  val n_atoms : store -> t -> int
  val marked : store -> t -> bool
  val set_marked : store -> t -> bool -> unit
  val attached : store -> t -> bool
  val set_attached : store -> t -> bool -> unit
  val removable : store -> t -> bool
  val dead : store -> t -> bool
  val set_dead : store -> t -> bool -> unit
  val dealloc : store -> t -> unit
  val proof_step : store -> t -> int32
  val activity : store -> t -> float
  val set_activity : store -> t -> float -> unit
  val iter : store -> f:(atom -> unit) -> t -> unit
  val fold : store -> f:('a -> atom -> 'a) -> 'a -> t -> 'a
  val for_all : store -> f:(atom -> bool) -> t -> bool
  val atoms_a : store -> t -> atom array
  val lits_l : store -> t -> Lit.t list
  val lits_a : store -> t -> Lit.t array
  val lits_iter : store -> t -> Lit.t Iter.t
  val short_name : store -> t -> string
  val pp : store -> Format.formatter -> t -> unit
  val debug : store -> Format.formatter -> t -> unit
end

val alloc_var_uncached_ : ?default_pol:bool -> t -> Lit.t -> var
val alloc_var : t -> ?default_pol:bool -> Lit.t -> var * bool
val clear_var : t -> var -> unit
val atom_of_var_ : var -> bool -> atom
val alloc_atom : t -> ?default_pol:bool -> Lit.t -> atom
val find_atom : t -> Lit.t -> atom option
