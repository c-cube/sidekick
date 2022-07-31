open Sidekick_core
open Sigs

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

  val equal : t -> t -> same_sign
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
  val marked : store -> var -> same_sign
  val set_default_pol : store -> var -> same_sign -> unit
  val default_pol : store -> var -> same_sign
  val heap_idx : store -> var -> int
  val set_heap_idx : store -> var -> int -> unit
end

module Atom : sig
  type t = atom

  val equal : t -> t -> same_sign
  val compare : t -> t -> int
  val hash : t -> int
  val to_int : t -> int
  val of_int_unsafe : int -> t
  val neg : t -> t
  val sign : t -> same_sign
  val of_var : var -> t
  val var : t -> var
  val pa : var -> t
  val na : var -> t

  module AVec = Sidekick_sat__Base_types_.Atom0.AVec
  module ATbl = Sidekick_sat__Base_types_.Atom0.ATbl

  val lit : store -> atom -> Lit.t
  val mark : store -> atom -> unit
  val unmark : store -> atom -> unit
  val marked : store -> atom -> same_sign
  val watched : store -> atom -> CVec.t
  val is_true : store -> atom -> same_sign
  val set_is_true : store -> atom -> same_sign -> unit
  val is_false : store -> t -> same_sign
  val has_value : store -> atom -> same_sign
  val reason : store -> t -> var_reason option
  val level : store -> t -> int
  val marked_both : store -> atom -> same_sign
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

  val equal : t -> t -> same_sign
  val compare : t -> t -> int
  val hash : t -> int
  val to_int : t -> int
  val of_int_unsafe : int -> t

  module Tbl : Hashtbl.S with type key = t
  module CVec = Base_types_.CVec

  val make_a : store -> removable:same_sign -> atom array -> int32 -> t
  val make_l : store -> removable:same_sign -> atom list -> int32 -> t
  val n_atoms : store -> t -> int
  val marked : store -> t -> same_sign
  val set_marked : store -> t -> same_sign -> unit
  val attached : store -> t -> same_sign
  val set_attached : store -> t -> same_sign -> unit
  val removable : store -> t -> same_sign
  val dead : store -> t -> same_sign
  val set_dead : store -> t -> same_sign -> unit
  val dealloc : store -> t -> unit
  val proof_step : store -> t -> int32
  val activity : store -> t -> float
  val set_activity : store -> t -> float -> unit
  val iter : store -> f:(atom -> unit) -> t -> unit
  val fold : store -> f:('a -> atom -> 'a) -> 'a -> t -> 'a
  val for_all : store -> f:(atom -> same_sign) -> t -> same_sign
  val atoms_a : store -> t -> atom array
  val lits_l : store -> t -> Lit.t list
  val lits_a : store -> t -> Lit.t array
  val lits_iter : store -> t -> Lit.t Iter.t
  val short_name : store -> t -> string
  val pp : store -> Format.formatter -> t -> unit
  val debug : store -> Format.formatter -> t -> unit
end

val alloc_var_uncached_ : ?default_pol:same_sign -> t -> Lit.t -> var
val alloc_var : t -> ?default_pol:same_sign -> Lit.t -> var * same_sign
val clear_var : t -> var -> unit
val atom_of_var_ : var -> same_sign -> atom
val alloc_atom : t -> ?default_pol:same_sign -> Lit.t -> atom
val find_atom : t -> Lit.t -> atom option
