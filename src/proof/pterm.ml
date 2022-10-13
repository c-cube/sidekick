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
  | P_apply r ->
    Fmt.fprintf out "%s{@[" r.rule_name;
    if r.premises <> [] then
      Fmt.fprintf out "@ :prem %a" Fmt.Dump.(list int) r.premises;
    if r.term_args <> [] then
      Fmt.fprintf out "@ :ts %a" Fmt.Dump.(list Term.pp) r.term_args;
    Fmt.fprintf out "@]}"
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
module Dec = Ser_decode

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

let deser_apply_rule (t_read : Term.Trace_reader.t) : rule_apply Ser_decode.t =
  let open Dec.Infix in
  let tst = Term.Trace_reader.store t_read in

  let dec_t =
    let* i = Dec.int in
    match Term.Trace_reader.read_term_err t_read i with
    | Ok t -> Dec.return t
    | Error e -> Dec.fail_err e
  in

  let dec_lit : Lit.t Dec.t =
    let+ sign, t = Dec.tup2 Dec.bool dec_t in
    Lit.atom ~sign tst t
  in
  let dec_premise : step_id Dec.t = Dec.int in
  let dec_indice : step_id Dec.t = Dec.int in
  let dec_subst : _ Dec.t = Dec.delay (fun () -> assert false (* TODO *)) in

  let+ rule_name = Dec.dict_field "name" Dec.string
  and+ lit_args = Dec.dict_field_or [] "lits" (Dec.list dec_lit)
  and+ term_args = Dec.dict_field_or [] "t" (Dec.list dec_t)
  and+ subst_args = Dec.dict_field_or [] "su" (Dec.list dec_subst)
  and+ indices = Dec.dict_field_or [] "idx" (Dec.list dec_indice)
  and+ premises = Dec.dict_field_or [] "ps" (Dec.list dec_premise) in

  { rule_name; lit_args; subst_args; term_args; premises; indices }

let rec deser (t_read : Term.Trace_reader.t) : t Ser_decode.t =
  let open Dec.Infix in
  let* l = Dec.list Dec.any in
  match l with
  | [ V.Int 0; v ] ->
    let+ i = Dec.reflect_or_fail Dec.int v in
    P_ref i
  | [ V.Int 1; v ] ->
    let+ i = Dec.reflect_or_fail Dec.int v in
    P_local i
  | [ V.Int 2; v ] ->
    let+ r = Dec.reflect_or_fail (deser_apply_rule t_read) v in
    P_apply r
  | [ V.Int 3; bs; body ] ->
    let dec_b = Dec.tup2 Dec.int (deser t_read) in
    let+ bs = Dec.reflect_or_fail (Dec.list dec_b) bs
    and+ body = Dec.reflect_or_fail (deser t_read) body in
    P_let (bs, body)
  | _ -> Dec.failf "unknown proof-term %a" (Fmt.Dump.list V.pp) l
