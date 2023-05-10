(** Reason for assignment *)

(** Reason for assignment *)
type t = TVar.reason =
  | Decide of { level: int }
  | Propagate of {
      level: int;
      hyps: TVar.Vec_of.t;
      proof: Sidekick_proof.step_id;
    }
(* TODO: merge is also a reason *)

include Sidekick_sigs.PRINT with type t := t

val decide : int -> t
val propagate_v : TVar.store -> TVar.Vec_of.t -> Sidekick_proof.step_id -> t
val propagate_l : TVar.store -> TVar.t list -> Sidekick_proof.step_id -> t
val level : t -> int
