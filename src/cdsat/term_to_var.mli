(** Conversion from terms to variables.

   Terms are context free and can undergo simplification, rewriting, etc.
   In contrast, CDSAT is concerned with the stateful manipulation of a finite
   set of variables and their assignment in the current (partial) model.
 *)

type t
(** The converter *)

val create : TVar.store -> t

(** {2 Conversion} *)

val convert : t -> Term.t -> TVar.t
(** Convert a term into a variable.
    This will fail if there is no hook that recognizes the term (meaning the
    term is not handled by any theory) *)

(** {2 Hooks}

    Hooks are responsible for converting {b some} terms (the terms their theory
    knows) into variables. *)

type hook = { conv: t -> Term.t -> TVar.theory_view option } [@@unboxed]
(** A hook, responsible to keep some internal state and assigning a theory
    view if it "accepts" the term. A term that is recognized by no hook
    cannot be turned into a variable. *)

val add_hook : t -> hook -> unit
