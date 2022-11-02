(** 1-Watch Scheme *)

type t

val make : TVar.store -> TVar.t list -> t

val make_a : TVar.store -> TVar.t array -> t
(** owns the array *)

val alive : t -> bool
val kill : t -> unit

val iter : t -> TVar.t Iter.t
(** current watch(es) *)

val init : t -> TVar.t -> on_all_set:(unit -> unit) -> unit
(** [init w t ~on_all_set] initializes [w] (the watchlist) for
    var [t], by finding an unassigned TVar.t in the watchlist and
    registering [t] to it.
    If all vars are set, then it watches the one with the highest level
    and call [on_all_set ()]
  *)

val update :
  t -> TVar.t -> watch:TVar.t -> on_all_set:(unit -> unit) -> Watch_res.t
(** [update w t ~watch ~on_all_set] updates [w] after [watch]
    has been assigned. It looks for another TVar.t in [w] for [t] to watch.
    If all vars are set, then it calls [on_all_set ()]
*)
