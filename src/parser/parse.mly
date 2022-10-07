
%{

open struct
  module A = Ast_term
end

%}

%token <string> ID
%token <string> INT
%token <string> SYMBOL
%token <string> HASH

%token <string> ERROR

%token LET
%token IN
%token AND
%token EQDEF
%token COLON
%token FUNCTION
%token PI
%token ARROW
%token DOT

%token SEMICOLON

%token LPAREN
%token RPAREN
/* TODO: implicit arguments in def */
%token LBRACE
%token RBRACE

%token DEF
%token THEOREM
%token BY
%token EXACT
%token HAVE

%token EOF

%start <Ast_term.term> top_term
%start <Ast_term.decl> top_decl
%start <Ast_term.decl list> top_decls

%%

top_decls: d=decl* EOF { d }
top_decl: d=decl EOF { d }
top_term: t=term EOF { t }

decl:
| h=HASH t=term SEMICOLON {
  let loc = Loc.of_lexloc $loc in
  let h = String.sub h 1 (String.length h-1) in
  A.decl_hash ~loc h t
}
| DEF name=name args=ty_var_group* ty_ret=optional_ty EQDEF rhs=term SEMICOLON {
  let loc = Loc.of_lexloc $loc in
  A.decl_def ~loc name args ?ty_ret rhs
}
| THEOREM name=name EQDEF goal=term proof=proof SEMICOLON {
  let loc = Loc.of_lexloc $loc in
  A.decl_theorem ~loc name goal proof
}

proof:
| BY t=term {
  let loc = Loc.of_lexloc $loc in
  A.proof_by ~loc t
}
| EXACT t=term {
  let loc = Loc.of_lexloc $loc in
  A.proof_exact ~loc t
}
| LBRACE steps=proof_step+ ret=proof RBRACE {
  let loc = Loc.of_lexloc $loc in
  A.proof_steps ~loc steps ret
}

proof_step:
| HAVE name=name EQDEF goal=term proof=proof SEMICOLON {
  let loc = Loc.of_lexloc $loc in
  A.step ~loc name goal proof
}

tyvar:
| name=name ty=optional_ty { A.var ?ty name }

ty_var_group:
| name=name { A.VG_untyped name }
| LPAREN names=name+ COLON ty=term RPAREN {
  A.VG_typed {names; ty}
}

%inline optional_ty:
| { None }
| COLON t=term { Some t }

term:
| t=binder_term { t }
| LET bs=let_bindings IN rhs=term {
  let loc = Loc.of_lexloc $loc in
  A.mk_let ~loc bs rhs
}

let_binding:
| x=tyvar EQDEF t=term {x,t}

let_bindings:
| b=let_binding { [b] }
| b=let_binding AND l=let_bindings { b::l }

binder_term:
| t=sym_term { t }
| FUNCTION vars=ty_var_group+ DOT rhs=binder_term {
  let loc = Loc.of_lexloc $loc in
  A.mk_lam ~loc vars rhs
}
| PI vars=ty_var_group+ DOT rhs=binder_term {
  let loc = Loc.of_lexloc $loc in
  A.mk_pi ~loc vars rhs
}

sym_term:
| t=arrow_term { t }
| t=arrow_term sym=SYMBOL u=arrow_term {
  let locsym = Loc.of_lexloc $loc(sym) in
  A.mk_app (A.mk_var ~loc:locsym sym) [t;u]
}

arrow_term:
| t=apply_term { t }
| t=apply_term ARROW u=arrow_term {
  let loc = Loc.of_lexloc $loc in
  A.mk_arrow ~loc [t] u
}

apply_term:
| t=atomic_term { t }
| f=atomic_term args=atomic_term+ {
  A.mk_app f args
}

(* TODO: lambda, pi, arrow *)


atomic_term:
| v=name {
  let loc = Loc.of_lexloc $loc in
  A.mk_var ~loc v
}
| i=INT {
  let loc = Loc.of_lexloc $loc in
  A.mk_int ~loc i
}
| LPAREN t=term RPAREN { t }
| err=ERROR {
  let loc = Loc.of_lexloc $loc in
  A.mk_error ~loc err
}

name:
| x=ID { x }

%%



