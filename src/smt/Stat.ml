
type t = {
  mutable num_clause_push  : int;
  mutable num_clause_tautology  : int;
  mutable num_propagations  : int;
}

let create () : t = {
  num_clause_push = 0;
  num_clause_tautology = 0;
  num_propagations = 0;
}
