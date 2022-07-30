open Types_

type t = explanation

let rec pp out (e : explanation) =
  match e with
  | E_trivial -> Fmt.string out "reduction"
  | E_lit lit -> Lit.pp out lit
  | E_congruence (n1, n2) ->
    Fmt.fprintf out "(@[congruence@ %a@ %a@])" E_node.pp n1 E_node.pp n2
  | E_merge (a, b) ->
    Fmt.fprintf out "(@[merge@ %a@ %a@])" E_node.pp a E_node.pp b
  | E_merge_t (a, b) ->
    Fmt.fprintf out "(@[<hv>merge@ @[:n1 %a@]@ @[:n2 %a@]@])" Term.pp_debug a
      Term.pp_debug b
  | E_theory (t, u, es, _) ->
    Fmt.fprintf out "(@[th@ :t `%a`@ :u `%a`@ :expl_sets %a@])" Term.pp_debug t
      Term.pp_debug u
      (Util.pp_list
      @@ Fmt.Dump.triple Term.pp_debug Term.pp_debug (Fmt.Dump.list pp))
      es
  | E_and (a, b) -> Format.fprintf out "(@[<hv1>and@ %a@ %a@])" pp a pp b

let mk_trivial : t = E_trivial
let[@inline] mk_congruence n1 n2 : t = E_congruence (n1, n2)

let[@inline] mk_merge a b : t =
  if E_node.equal a b then
    mk_trivial
  else
    E_merge (a, b)

let[@inline] mk_merge_t a b : t =
  if Term.equal a b then
    mk_trivial
  else
    E_merge_t (a, b)

let[@inline] mk_lit l : t = E_lit l
let[@inline] mk_theory t u es pr = E_theory (t, u, es, pr)

let rec mk_list l =
  match l with
  | [] -> mk_trivial
  | [ x ] -> x
  | E_trivial :: tl -> mk_list tl
  | x :: y ->
    (match mk_list y with
    | E_trivial -> x
    | y' -> E_and (x, y'))
