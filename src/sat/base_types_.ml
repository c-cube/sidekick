(* a boolean variable (positive int) *)
module Var0 : sig
  include Int_id.S
end = struct
  include Int_id.Make ()
end

type var = Var0.t

(* a signed atom. +v is (v << 1), -v is (v<<1 | 1) *)
module Atom0 : sig
  include Int_id.S

  val neg : t -> t
  val sign : t -> bool
  val of_var : var -> t
  val var : t -> var
  val pa : var -> t
  val na : var -> t

  module ATbl : CCHashtbl.S with type key = t
end = struct
  include Int_id.Make ()

  let[@inline] neg i = i lxor 1
  let[@inline] sign i = i land 1 = 0
  let[@inline] pa v = (v : var :> int) lsl 1
  let of_var = pa
  let[@inline] var a = Var0.of_int_unsafe (a lsr 1)
  let[@inline] na v = ((v : var :> int) lsl 1) lor 1

  module ATbl = CCHashtbl.Make (CCInt)
end

module Clause0 : sig
  include Int_id.S
  module Tbl : Hashtbl.S with type key = t
end = struct
  include Int_id.Make ()
  module Tbl = Util.Int_tbl
end

type atom = Atom0.t
type clause = Clause0.t
type var_reason = Decision | Bcp of clause | Bcp_lazy of clause lazy_t

module ATbl = Atom0.ATbl
(** Hashtbl of atoms *)
