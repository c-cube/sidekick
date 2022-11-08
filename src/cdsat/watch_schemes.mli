(** Watch schemes *)

module Make (Ev : sig
  type t
end) : sig
  type t
  type handle

  val create : TVar.store -> t
  (** New set of watchers *)

  val watch2 :
    t -> TVar.t array -> Ev.t -> f:(unit:bool -> Ev.t -> unit) -> handle
  (** 2-watch scheme on these variables. *)

  val watch1 :
    t -> TVar.t array -> Ev.t -> f:(unit:bool -> Ev.t -> unit) -> handle
  (** 1-watch scheme on these variables. *)

  val kill : t -> handle -> unit
  (** Disable watch *)

  val gc : t -> unit
  (** Reclaim slots that have been killed *)

  val update : t -> TVar.t -> f:(unit:bool -> Ev.t -> unit) -> unit
  (** [update watches v ~f] updates watchers that contain [v],
      and calls [f ~unit ev] for each event whose watch just saturated.
      [unit] is true if the watch is a 2-watch that became unit; [false] in
      any other case (including a fully saturated 2-watch) *)
end
