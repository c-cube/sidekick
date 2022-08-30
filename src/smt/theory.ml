(** Signatures for theory plugins *)

(** A theory

      Theories are abstracted over the concrete implementation of the solver,
      so they can work with any implementation.

      Typically a theory should be a functor taking an argument containing
      a [SOLVER_INTERNAL] or even a full [SOLVER],
      and some additional views on terms, literals, etc.
      that are specific to the theory (e.g. to map terms to linear
      expressions).
      The theory can then be instantiated on any kind of solver for any
      term representation that also satisfies the additional theory-specific
      requirements. Instantiated theories (ie values of type {!SOLVER.theory})
      can be added to the solver.
  *)
module type S = sig
  type t

  val name : string
  val create_and_setup : id:Theory_id.t -> Solver_internal.t -> t
  val push_level : t -> unit
  val pop_levels : t -> int -> unit
end

type t = (module S)
(** A theory that can be used for this particular solver. *)

type 'a p = (module S with type t = 'a)
(** A theory that can be used for this particular solver, with state
      of type ['a]. *)

(** Name of the theory *)
let name (th : t) =
  let (module T) = th in
  T.name

let make (type st) ~name ~create_and_setup ?(push_level = fun _ -> ())
    ?(pop_levels = fun _ _ -> ()) () : t =
  let module Th = struct
    type t = st

    let name = name
    let create_and_setup = create_and_setup
    let push_level = push_level
    let pop_levels = pop_levels
  end in
  (module Th)
