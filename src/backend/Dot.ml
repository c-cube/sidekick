(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** Output interface for the backend *)
module type S = Backend_intf.S

(** Input module for the backend *)
module type Arg = sig

  type atom
  (* Type of atoms *)

  type store
  type hyp
  type lemma
  type assumption
  (** Types for hypotheses, lemmas, and assumptions. *)

  val print_atom : store -> Format.formatter -> atom -> unit
  (** Printing function for atoms *)

  val hyp_info : store -> hyp -> string * string option * (Format.formatter -> unit -> unit) list
  val lemma_info : store -> lemma -> string * string option * (Format.formatter -> unit -> unit) list
  val assumption_info : store -> assumption -> string * string option * (Format.formatter -> unit -> unit) list
  (** Functions to return information about hypotheses and lemmas *)

end

module Default(S : Sidekick_sat.S) = struct
  module Atom = S.Atom
  module Clause = S.Clause

  type store = S.solver
  let print_atom = S.Atom.pp

  let hyp_info store c =
    "hypothesis", Some "LIGHTBLUE",
    [ fun fmt () -> Format.fprintf fmt "%s" @@ S.Clause.short_name store c]

  let lemma_info store c =
    "lemma", Some "BLUE",
    [ fun fmt () -> Format.fprintf fmt "%s" @@ S.Clause.short_name store c]

  let assumption_info store c =
    "assumption", Some "PURPLE",
    [ fun fmt () -> Format.fprintf fmt "%s" @@ S.Clause.short_name store c]

end

(** Functor to provide dot printing *)
module Make(S : Sidekick_sat.S)(A : Arg with type atom := S.atom
                                and type hyp := S.clause
                                and type lemma := S.clause
                                and type store := S.store
                                and type assumption := S.clause) = struct
  module Atom = S.Atom
  module Clause = S.Clause
  module P = S.Proof

  let node_id store n = S.Clause.short_name store n.P.conclusion
  let proof_id store p = node_id store (P.expand store p)
  let res_nn_id store n1 n2 = node_id store n1 ^ "_" ^ node_id store n2 ^ "_res"
  let res_np_id store n1 n2 = node_id store n1 ^ "_" ^ proof_id store n2 ^ "_res"

  let print_clause store fmt c =
    let v = S.Clause.atoms_a store c in
    if Array.length v = 0 then
      Format.fprintf fmt "⊥"
    else
      let n = Array.length v in
      for i = 0 to n - 1 do
        Format.fprintf fmt "%a" (A.print_atom store) v.(i);
        if i < n - 1 then
          Format.fprintf fmt ", "
      done

  let print_edge fmt i j =
    Format.fprintf fmt "%s -> %s;@\n" j i

  let print_edges store fmt n =
    match P.(n.step) with
    | P.Hyper_res {P.hr_steps=[];_} -> assert false (* NOTE: should never happen *)
    | P.Hyper_res {P.hr_init; hr_steps=((_,p0)::_) as l} ->
      print_edge fmt (res_np_id store n p0) (proof_id store hr_init);
      List.iter
        (fun (_,p2) -> print_edge fmt (res_np_id store n p2) (proof_id store p2))
        l;
    | _ -> ()

  let table_options fmt color =
    Format.fprintf fmt "BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" BGCOLOR=\"%s\"" color

  let table store fmt (c, rule, color, l) =
    Format.fprintf fmt "<TR><TD colspan=\"2\">%a</TD></TR>" (print_clause store) c;
    match l with
    | [] ->
      Format.fprintf fmt "<TR><TD BGCOLOR=\"%s\" colspan=\"2\">%s</TD></TR>" color rule
    | f :: r ->
      Format.fprintf fmt "<TR><TD BGCOLOR=\"%s\" rowspan=\"%d\">%s</TD><TD>%a</TD></TR>"
        color (List.length l) rule f ();
      List.iter (fun f -> Format.fprintf fmt "<TR><TD>%a</TD></TR>" f ()) r

  let print_dot_node store fmt id color c rule rule_color l =
    Format.fprintf fmt "%s [shape=plaintext, label=<<TABLE %a>%a</TABLE>>];@\n"
      id table_options color (table store) (c, rule, rule_color, l)

  let print_dot_res_node store fmt id a =
    Format.fprintf fmt "%s [label=<%a>];@\n" id (A.print_atom store) a

  let ttify f c = fun fmt () -> f fmt c

  let print_contents store fmt n =
    match P.(n.step) with
    (* Leafs of the proof tree *)
    | P.Hypothesis _ ->
      let rule, color, l = A.hyp_info store P.(n.conclusion) in
      let color = match color with None -> "LIGHTBLUE" | Some c -> c in
      print_dot_node store fmt (node_id store n) "LIGHTBLUE" P.(n.conclusion) rule color l
    | P.Assumption ->
      let rule, color, l = A.assumption_info store P.(n.conclusion) in
      let color = match color with None -> "LIGHTBLUE" | Some c -> c in
      print_dot_node store fmt (node_id store n) "LIGHTBLUE" P.(n.conclusion) rule color l
    | P.Lemma _ ->
      let rule, color, l = A.lemma_info store P.(n.conclusion) in
      let color = match color with None -> "YELLOW" | Some c -> c in
      print_dot_node store fmt (node_id store n) "LIGHTBLUE" P.(n.conclusion) rule color l

    (* Tree nodes *)
    | P.Duplicate (p, l) ->
      print_dot_node store fmt (node_id store n) "GREY" P.(n.conclusion) "Duplicate" "GREY"
        ((fun fmt () -> (Format.fprintf fmt "%s" (node_id store n))) ::
         List.map (ttify @@ A.print_atom store) l);
      print_edge fmt (node_id store n) (node_id store (P.expand store p))
    | P.Hyper_res {P.hr_steps=l; _} ->
      print_dot_node store fmt (node_id store n) "GREY" P.(n.conclusion) "Resolution" "GREY"
        [(fun fmt () -> (Format.fprintf fmt "%s" (node_id store n)))];
      List.iter
        (fun (a,p2) ->
          print_dot_res_node store fmt (res_np_id store n p2) a;
          print_edge fmt (node_id store n) (res_np_id store n p2))
        l

  let print_node store fmt n =
    print_contents store fmt n;
    print_edges store fmt n

  let pp store fmt p =
    Format.fprintf fmt "digraph proof {@\n";
    P.fold store (fun () -> print_node store fmt) () p;
    Format.fprintf fmt "}@."

end

