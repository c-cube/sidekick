(** Main Signatures.

    Theories and concrete solvers rely on an environment that defines
    several important types:

      - types
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
    - a bridge to some SAT solver

    In this module we define most of the main signatures used
    throughout Sidekick.
*)

module Fmt = CCFormat

(** {2 Re-exports from core-logic} *)

module Const = Sidekick_core_logic.Const
module Str_const = Sidekick_core_logic.Str_const

module Term = struct
  include Sidekick_core_logic.Term
  include Sidekick_core_logic.T_builtins
  include T_printer
  module Tracer = T_tracer
  module Trace_reader = T_trace_reader
  module Ref = T_ref
end

(** {2 view} *)

module Bool_view = Bool_view
module CC_view = CC_view
module Default_cc_view = Default_cc_view

(** {2 Main modules} *)

module Bvar = Sidekick_core_logic.Bvar
module Lit = Lit
module Subst = Sidekick_core_logic.Subst
module Var = Sidekick_core_logic.Var
module Box = Box
module Clause_tracer = Clause_tracer
module Gensym = Gensym

exception Resource_exhausted

(** {2 Const decoders for traces} *)

let const_decoders =
  List.flatten
    [
      Sidekick_core_logic.T_builtins.const_decoders;
      T_ref.const_decoders;
      Box.const_decoders;
    ]
