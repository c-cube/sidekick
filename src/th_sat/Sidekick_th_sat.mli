(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
*)

(** Sat solver

    This modules instanciates a pure sat solver using integers to represent
    atomic propositions.
*)

module Th = Th_sat

include module type of Sidekick_sat.Make(Th)
(** A functor that can generate as many solvers as needed. *)

