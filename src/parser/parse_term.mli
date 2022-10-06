module A = Ast_term

val p : A.term Parser_comb.t
(** Term parser *)

val of_string : string -> A.term Parser_comb.or_error
val of_string_exn : string -> A.term
val of_string_l : string -> A.term list Parser_comb.or_error
val of_string_l_exn : string -> A.term list
