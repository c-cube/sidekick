
type t = {
  mutable num_cst_expanded  : int;
  mutable num_uty_expanded  : int;
  mutable num_clause_push  : int;
  mutable num_clause_tautology  : int;
  mutable num_propagations  : int;
  mutable num_unif  : int;
}

let create () : t = {
  num_cst_expanded = 0;
  num_uty_expanded = 0;
  num_clause_push = 0;
  num_clause_tautology = 0;
  num_propagations = 0;
  num_unif = 0;
}
