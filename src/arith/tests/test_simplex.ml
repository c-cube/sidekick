module Fmt = CCFormat
module QC = QCheck

module Var = struct
  include CCInt

  let pp out x = Format.fprintf out "X_%d" x

  let rand n : t QC.arbitrary = QC.make ~print:(Fmt.to_string pp) @@ QC.Gen.(0--n)
  type lit = int
  let pp_lit = Fmt.int

  module Fresh = struct
    type var = t
    type t = int ref
    let copy r = ref !r
    let create() = ref ~-1
    let fresh r = decr r; !r
  end
end

module L = Sidekick_arith_lra.Linear_expr.Make(struct include Q let pp=pp_print end)(Var)
module Spl = Sidekick_arith_lra.Simplex.Make_full_for_expr(Var)(L)
module Var_map = Spl.Var_map

let rand_n low n : Z.t QC.arbitrary =
  QC.map ~rev:Z.to_int Z.of_int QC.(low -- n)

let rand_q : Q.t QC.arbitrary =
  let n1 = rand_n ~-100_000 100_000 in
  let n2 = rand_n 1 40_000 in
  let qc =
    QC.map ~rev:(fun q -> Q.num q, Q.den q)
      (fun (x,y) -> Q.make x y)
      (QC.pair n1 n2)
  in
  (* avoid [undef] when shrinking *)
  let shrink q yield =
    CCOpt.get_exn qc.QC.shrink q (fun x -> if Q.is_real x then yield x)
  in
  QC.set_shrink shrink qc

type subst = Spl.L.subst

(* NOTE: should arrive in qcheck at some point *)
let filter_shrink (f:'a->bool) (a:'a QC.arbitrary) : 'a QC.arbitrary =
  match a.QC.shrink with
    | None -> a
    | Some shr ->
      let shr' x yield = shr x (fun y -> if f y then yield y) in
      QC.set_shrink shr' a

module Comb = struct
  include Spl.L.Comb

  let rand n : t QC.arbitrary =
    let a =
      QC.map_same_type (fun e -> if is_empty e then monomial1 0 else e) @@
      QC.map ~rev:to_list of_list @@
      QC.list_of_size QC.Gen.(1--n) @@ QC.pair rand_q (Var.rand 10)
    in
    filter_shrink (fun e -> not (is_empty e)) a
end

module Expr = struct
  include Spl.L.Expr

  let rand n : t QC.arbitrary =
    QC.map ~rev:(fun e->comb e, const e) (CCFun.uncurry make) @@
    QC.pair (Comb.rand n) rand_q
end

module Constr = struct
  include Spl.L.Constr

  let shrink c : t QC.Iter.t =
    let open QC.Iter in
    CCOpt.map_or ~default:empty
      (fun s -> s c.expr >|= fun expr -> {c with expr})
      (Expr.rand 5).QC.shrink

  let rand n : t QC.arbitrary =
    let gen =
      QC.Gen.(
        return of_expr <*>
          (Expr.rand n).QC.gen <*>
          oneofl Sidekick_arith_lra.Predicate.([Leq;Geq;Lt;Gt;Eq])
      )
    in
    QC.make ~print:(Fmt.to_string pp) ~shrink gen
end

module Problem = struct
  type t = Constr.t list

  module Infix = struct
    let (&&) = List.rev_append
  end
  include Infix

  let eval subst = List.for_all (L.Constr.eval subst)

  let pp out pb = Fmt.(hvbox @@ list ~sep:(return "@ @<1>∧ ") L.Constr.pp) out pb

  let rand ?min:(m=3) n : t QC.arbitrary =
    let n = max m (max n 6) in
    QC.list_of_size QC.Gen.(m -- n) @@ Constr.rand 10
end

let add_problem (t:Spl.t) (pb:Problem.t) : unit =
  (* TODO: use an arbitrary litteral if the tests do not check the unsat core,
           or else add litterals to the generated problem. *)
  let lit = assert false in
  List.iter (fun constr -> Spl.add_constr t constr lit) pb

let pp_subst : subst Fmt.printer =
  Fmt.(map Spl.L.Var_map.to_iter @@
    within "{" "}" @@ hvbox @@ iter ~sep:(return ",@ ") @@
    pair ~sep:(return "@ @<1>→ ") Var.pp Q.pp_print
  )

let check_invariants =
  let prop pb =
    let simplex = Spl.create (Var.Fresh.create()) in
    add_problem simplex pb;
    Spl.check_invariants simplex
  in
  QC.Test.make ~long_factor:10 ~count:50 ~name:"simplex_invariants" (Problem.rand 20) prop

let check_invariants_after_solve =
  let prop pb =
    let simplex = Spl.create (Var.Fresh.create()) in
    add_problem simplex pb;
    ignore (Spl.solve simplex);
    if Spl.check_invariants simplex then true
    else (
      QC.Test.fail_reportf "(@[bad-invariants@ %a@])" Spl.pp_full_state simplex
    )
  in
  QC.Test.make ~long_factor:10 ~count:50 ~name:"simplex_invariants_after_solve" (Problem.rand 20) prop

let check_sound =
  let prop pb =
    let simplex = Spl.create (Var.Fresh.create()) in
    add_problem simplex pb;
    let old_simp = Spl.copy simplex in
    begin match Spl.solve simplex with
      | Spl.Solution subst ->
        if Problem.eval subst pb then true
        else (
          QC.Test.fail_reportf
            "(@[<hv>bad-solution@ :problem %a@ :sol %a@ :simplex-after  %a@ :simplex-before %a@])"
            Problem.pp pb pp_subst subst Spl.pp_full_state simplex Spl.pp_full_state old_simp
        )
      | Spl.Unsatisfiable cert ->
        begin match Spl.check_cert simplex cert with
          | `Ok _ -> true
          | `Bad_bounds (low, up) ->
            QC.Test.fail_reportf
              "(@[<hv>bad-certificat@ :problem %a@ :cert %a@ :low %s :up %s@ :simplex-after  %a@ :simplex-before %a@])"
              Problem.pp pb Spl.pp_cert cert low up Spl.pp_full_state simplex Spl.pp_full_state old_simp
          | `Diff_not_0 e ->
            QC.Test.fail_reportf
              "(@[<hv>bad-certificat@ :problem %a@ :cert %a@ :diff %a@ :simplex-after  %a@ :simplex-before %a@])"
              Problem.pp pb Spl.pp_cert cert Comb.pp (Comb.of_map e) Spl.pp_full_state simplex Spl.pp_full_state old_simp
        end
    end
  in
  QC.Test.make ~long_factor:10 ~count:300 ~name:"simplex_sound" (Problem.rand 20) prop

let check_scalable =
  let prop pb =
    let simplex = Spl.create (Var.Fresh.create()) in
    add_problem simplex pb;
    ignore (Spl.solve simplex);
    true
  in
  QC.Test.make ~long_factor:2 ~count:10 ~name:"simplex_scalable" (Problem.rand ~min:150 150) prop


let props = [
  check_invariants;
  check_sound;
  check_scalable;
]
