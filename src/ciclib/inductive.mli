module T = Term

type cstor = Types_.cstor = { c_name: string; c_ty: T.t }

type spec = Types_.spec = {
  name: string;
  univ_params: Level.var list;
  n_params: int;
  ty: T.t;
  cstors: cstor list;
}
(** Inductive spec *)

val pp_cstor : cstor Fmt.printer
val pp_spec : spec Fmt.printer

val is_valid : spec -> bool
(** Check for validity of the spec *)
