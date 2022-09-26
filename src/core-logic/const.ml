open Types_

type view = const_view = ..

module Ops = struct
  type t = const_ops = {
    pp: const_view Fmt.printer;  (** Pretty-print constant *)
    equal: const_view -> const_view -> bool;
    hash: const_view -> int;  (** Hash constant *)
    ser: (term -> Ser_value.t) -> const_view -> string * Ser_value.t;
  }
end

type t = const = { c_view: view; c_ops: Ops.t; c_ty: term }

let[@inline] view self = self.c_view
let[@inline] ty self = self.c_ty

let[@inline] equal (a : t) b =
  a.c_ops.equal a.c_view b.c_view && Term_.equal a.c_ty b.c_ty

let[@inline] hash (a : t) : int =
  H.combine2 (a.c_ops.hash a.c_view) (Term_.hash a.c_ty)

let pp out (a : t) = a.c_ops.pp out a.c_view
let ser ~ser_t (self : t) = self.c_ops.ser ser_t self.c_view
let make c_view c_ops ~ty:c_ty : t = { c_view; c_ops; c_ty }

type decoders =
  (string * Ops.t * (term Ser_decode.t -> view Ser_decode.t)) list
