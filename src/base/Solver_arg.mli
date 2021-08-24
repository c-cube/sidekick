
(** Concrete implementation of {!Sidekick_core.TERM}

    this module gathers most definitions above in a form
    that is compatible with what Sidekick expects for terms, functions, etc.
*)

open Base_types

include Sidekick_core.TERM
  with type Term.t = Term.t
   and type Fun.t = Fun.t
   and type Ty.t = Ty.t
   and type Term.store = Term.store
   and type Ty.store = Ty.store
