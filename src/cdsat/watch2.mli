(** 2-Watch Scheme *)

type t

val dummy : t
val make : TVar.t list -> t

val make_a : TVar.t array -> t
(** owns the array *)

val iter : t -> TVar.t Iter.t
(** current watch(es) *)

val init :
  TVar.store ->
  t ->
  TVar.t ->
  on_unit:(TVar.t -> unit) ->
  on_all_set:(unit -> unit) ->
  unit
(** [init tstore w t ~on_all_set] initializes [w] (the watchlist) for
    var [t], by finding an unassigned var in the watchlist and
    registering [t] to it.
    If exactly one TVar.t [u] is not set, then it calls [on_unit u].
    If all vars are set, then it watches the one with the highest level
    and call [on_all_set ()]
  *)

val update :
  TVar.store ->
  t ->
  TVar.t ->
  watch:TVar.t ->
  on_unit:(TVar.t -> unit) ->
  on_all_set:(unit -> unit) ->
  Watch_res.t
(** [update tstore w t ~watch ~on_all_set] updates [w] after [watch]
    has been assigned. It looks for another var in [w] for [t] to watch.
    If exactly one var [u] is not set, then it calls [on_unit u].
    If all vars are set, then it calls [on_all_set ()]
*)
