
exception Bad_atom
(** Exception raised if an atom cannot be created *)

type proof = unit
(** A empty type for proofs *)

type formula = int

type t = {
  mutable max_index: int;
  mutable max_fresh: int;
}

let create () : t = {
  max_index = 0;
  max_fresh= (-1);
}

module Form = struct
  type t = formula
  (** Atoms are represented as integers. [-i] begin the negation of [i].
      Additionally, since we nee dot be able to create fresh atoms, we
      use even integers for user-created atoms, and odd integers for the
      fresh atoms. *)

  let max_lit = max_int

  let hash (a:int) = a land max_int
  let equal (a:int) b = a=b
  let compare (a:int) b = Pervasives.compare a b

  (** Internal function for creating atoms.
      Updates the internal counters *)
  let make_ st i =
    if i <> 0 && (abs i) < max_lit then (
      st.max_index <- max st.max_index (abs i);
      i
    ) else (
      raise Bad_atom
    )

  (** A dummy atom *)
  let dummy = 0

  let neg a = - a

  let norm a =
    abs a, if a < 0 then
      Msat.Negated
    else
      Msat.Same_sign

  let print fmt a =
    Format.fprintf fmt "%s%s%d"
      (if a < 0 then "~" else "")
      (if a mod 2 = 0 then "v" else "f")
      ((abs a) / 2)

end

let abs = abs

let sign i = i > 0

let apply_sign b i = if b then i else Form.neg i

let set_sign b i = if b then abs i else Form.neg (abs i)

let make st i = Form.make_ st (2 * i)

let fresh st =
  st.max_fresh <- 1 + st.max_fresh;
  Form.make_ st (2 * st.max_fresh + 1)

(*
let iter: (t -> unit) -> unit = fun f ->
  for j = 1 to !max_index do
    f j
  done
*)

let assume _ _ = Msat.Theory_intf.Sat

let if_sat _ _ = Msat.Theory_intf.Sat
