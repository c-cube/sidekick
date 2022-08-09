(** View terms through the lens of a Congruence Closure *)

(** A view of a term fron the point of view of a congruence closure.

  - ['f] is the type of function symbols
  - ['t] is the type of terms
  - ['ts] is the type of sequences of terms (arguments of function application)
  *)
type ('f, 't, 'ts) t =
  | Bool of bool
  | App_fun of 'f * 'ts
  | App_ho of 't * 't
  | If of 't * 't * 't
  | Eq of 't * 't
  | Not of 't
  | Opaque of 't  (** do not enter *)

val map_view :
  f_f:('a -> 'b) ->
  f_t:('c -> 'd) ->
  f_ts:('e -> 'f) ->
  ('a, 'c, 'e) t ->
  ('b, 'd, 'f) t
(** Map function over a view, one level deep.
    Each function maps over a different type, e.g. [f_t] maps over terms *)

val iter_view :
  f_f:('a -> unit) ->
  f_t:('b -> unit) ->
  f_ts:('c -> unit) ->
  ('a, 'b, 'c) t ->
  unit
(** Iterate over a view, one level deep. *)
