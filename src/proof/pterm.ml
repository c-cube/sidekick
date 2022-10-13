type step_id = Step.id
type lit = Lit.t
type local_ref = Step.id

type rule_apply = {
  rule_name: string;
  lit_args: lit list;
  term_args: Term.t list;
  subst_args: Subst.t list;
  premises: step_id list;
  indices: int list;
}

type t =
  | P_ref of step_id
  | P_local of local_ref
  | P_let of (local_ref * t) list * t
  | P_apply of rule_apply

type delayed = unit -> t

let rec pp out = function
  | P_ref r -> Fmt.fprintf out "!%d" r
  | P_local id -> Fmt.fprintf out "s%d" id
  | P_apply r -> Fmt.fprintf out "%s" r.rule_name
  | P_let (bs, bod) ->
    let pp_b out (x, t) = Fmt.fprintf out "s%d := %a" x pp t in
    Fmt.fprintf out "(@[let %a@ in %a@])"
      (Util.pp_list ~sep:"; " pp_b)
      bs pp bod

let local_ref id = P_local id
let ref id = P_ref id
let[@inline] delay f = f
let dummy = ref Step.dummy

let let_ bs r =
  match bs with
  | [] -> r
  | _ -> P_let (bs, r)

let apply_rule ?(lits = []) ?(terms = []) ?(substs = []) ?(premises = [])
    ?(indices = []) rule_name : t =
  P_apply
    {
      rule_name;
      lit_args = lits;
      subst_args = substs;
      term_args = terms;
      premises;
      indices;
    }

module V = Ser_value

let ser_apply_rule (tracer : Term.Tracer.t) (r : rule_apply) : Ser_value.t =
  let { rule_name; lit_args; subst_args; term_args; premises; indices } = r in

  let enc_lit (lit : Lit.t) : V.t =
    let sign = Lit.sign lit in
    let id_t = Term.Tracer.emit tracer @@ Lit.term lit in
    V.(list [ bool sign; int id_t ])
  in

  let enc_t t = V.int (Term.Tracer.emit tracer t) in
  let enc_premise (p : step_id) = V.int p in
  let enc_indice (p : step_id) = V.int p in
  let enc_subst (_s : Subst.t) : V.t = assert false (* TODO *) in

  (* add a field [x, v] if [v] is not the empty list *)
  let add_ x v enc_v l =
    match v with
    | [] -> l
    | _ ->
      let v = V.list (List.map enc_v v) in
      (x, v) :: l
  in

  let l =
    [ "name", V.string rule_name ]
    |> add_ "lits" lit_args enc_lit
    |> add_ "su" subst_args enc_subst
    |> add_ "t" term_args enc_t
    |> add_ "ps" premises enc_premise
    |> add_ "idx" indices enc_indice
  in

  V.dict_of_list l

let rec to_ser (tracer : Term.Tracer.t) t : Ser_value.t =
  let recurse = to_ser tracer in
  V.(
    match t with
    | P_ref r -> list [ int 0; int r ]
    | P_local id -> list [ int 1; int id ]
    | P_apply r -> list [ int 2; ser_apply_rule tracer r ]
    | P_let (bs, bod) ->
      let ser_b (x, t) = list [ int x; recurse t ] in
      list [ int 3; list (List.map ser_b bs); recurse bod ])
