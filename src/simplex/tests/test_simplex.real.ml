
open CCMonomorphic

module Fmt = CCFormat
module QC = QCheck
module Log = Sidekick_util.Log
let spf = Printf.sprintf

module Var = struct
  include CCInt

  let pp out x = Format.fprintf out "X_%d" x

  let rand n : t QC.arbitrary = QC.make ~print:(Fmt.to_string pp) @@ QC.Gen.(0--n)
  type lit = int
  let pp_lit = Fmt.int
  let not_lit i = Some (- i)
end

module Spl = Sidekick_simplex.Make(struct
    module Q = Sidekick_zarith.Rational
    module Z = Sidekick_zarith.Int
    module Var = Var
    let mk_lit _ _ = assert false
  end)

let unwrap_opt_ msg = function
  | Some x -> x
  | None -> failwith msg

let rand_n low n : Z.t QC.arbitrary =
  QC.map ~rev:Z.to_int Z.of_int QC.(low -- n)

let rand_q_with u l : Q.t QC.arbitrary =
  let n1 = rand_n (~- u) u in
  let n2 = rand_n 1 l in
  let qc =
    QC.map ~rev:(fun q -> Q.num q, Q.den q)
      (fun (x,y) -> Q.make x y)
      (QC.pair n1 n2)
  in
  (* avoid [undef] when shrinking *)
  let shrink q yield =
    unwrap_opt_ "no shrinker" qc.QC.shrink q (fun x -> if Q.is_real x then yield x)
  in
  QC.set_shrink shrink qc

let rand_q = rand_q_with 200_000 40_000

module Step = struct
  module G = QC.Gen

  type t =
    | S_new_var of Var.t
    | S_define of Var.t * (Q.t * Var.t) list
    | S_leq of Var.t * Q.t
    | S_lt of Var.t * Q.t
    | S_geq of Var.t * Q.t
    | S_gt of Var.t * Q.t

  let pp_le out le =
    let pp_pair out (n,x) =
      if Q.equal Q.one n then Var.pp out x
      else Fmt.fprintf out "%a . %a" Q.pp_print n Var.pp x in
    Fmt.fprintf out "(@[%a@])"
      Fmt.(list ~sep:(return " +@ ") pp_pair) le

  let pp_ out = function
    | S_new_var v -> Fmt.fprintf out "(@[new-var %a@])" Var.pp v
    | S_define (v,le) -> Fmt.fprintf out "(@[define %a@ := %a@])" Var.pp v pp_le le
    | S_leq (x,n) -> Fmt.fprintf out "(@[upper %a <= %a@])" Var.pp x Q.pp_print n
    | S_lt (x,n) -> Fmt.fprintf out "(@[upper %a < %a@])" Var.pp x Q.pp_print n
    | S_geq (x,n) -> Fmt.fprintf out "(@[lower %a >= %a@])" Var.pp x Q.pp_print n
    | S_gt (x,n) -> Fmt.fprintf out "(@[lower %a > %a@])" Var.pp x Q.pp_print n

  (* check that a sequence is well formed *)
  let well_formed (l:t list) : bool =
    let rec aux vars = function
      | [] -> true
      | S_new_var v :: tl ->
        not (List.mem v vars) && aux (v::vars) tl
      | (S_leq (x,_) | S_lt (x,_) | S_geq (x,_) | S_gt (x,_)) :: tl ->
        List.mem x vars && aux vars tl
      | S_define (x,le) :: tl->
        not (List.mem x vars) &&
        List.for_all (fun (_,y) -> List.mem y vars) le &&
        aux (x::vars) tl
    in
    aux [] l

  let shrink_step self =
    let module S = QC.Shrink in
    match self with
    | S_new_var _
    | S_leq _ | S_lt _ | S_geq _ | S_gt _ -> QC.Iter.empty
    | S_define (x, le) ->
      let open QC.Iter in
      let* le = S.list le in
      if List.length le >= 2 then return (S_define (x,le)) else empty

  let rand_steps (n:int) : t list QC.Gen.t =
    let open G in
    let rec aux n vars acc =
      if n<=0 then return (List.rev acc)
      else (
        let* vars, proof_rule =
          frequency @@ List.flatten [
            (* add a bound *)
            (match vars with
             | [] -> []
             | vs ->
               let gen =
                 let+ x = oneofl vs
                 and+ kind = oneofl [`Leq;`Lt;`Geq;`Gt]
                 and+ n = rand_q.QC.gen in
                 vars, (match kind with
                     | `Lt -> S_lt(x,n)
                     | `Leq -> S_leq(x,n)
                     | `Gt -> S_gt(x,n)
                     | `Geq -> S_geq(x,n))
               in
               [6, gen]);
            (* make a new non-basic var *)
            (let gen =
               let v = List.length vars in
               return ((v::vars), S_new_var v)
             in
             [2, gen]);
            (* make a definition *)
            (if List.length vars>2
             then (
               let v = List.length vars in
               let gen =
                 let* vars' = G.shuffle_l vars in
                 let* n = 1 -- List.length vars' in
                 let vars' = CCList.take n vars' in
                 assert (List.length vars' = n);
                 let* coeffs = list_repeat n rand_q.gen in
                 let le = List.combine coeffs vars' in
                 return (v::vars, S_define (v, le))
               in
               [5, gen]
            ) else []);
          ]
        in
        aux (n-1) vars (proof_rule::acc)
      )
    in
    aux n [] []

  (* shrink a list but keep it well formed *)
  let shrink : t list QC.Shrink.t =
    QC.Shrink.(filter well_formed @@ list ~shrink:shrink_step)

  let gen_for n1 n2 =
    let open G in
    assert (n1 < n2);
    let* n = n1 -- n2 in
    rand_steps n

  let rand_for n1 n2 : t list QC.arbitrary =
    let print = Fmt.to_string (Fmt.Dump.list pp_) in
    QC.make ~shrink ~print (gen_for n1 n2)

  let rand : t list QC.arbitrary = rand_for 1 100
end

let on_propagate _ ~reason:_ = ()

(* add a single proof_rule to the simplexe *)
let add_step simplex (s:Step.t) : unit =
  begin match s with
    | Step.S_new_var v -> Spl.add_var simplex v
    | Step.S_leq (v,n) ->
      Spl.add_constraint simplex (Spl.Constraint.leq v n) 0 ~on_propagate
    | Step.S_lt (v,n) ->
      Spl.add_constraint simplex (Spl.Constraint.lt v n) 0 ~on_propagate
    | Step.S_geq (v,n) ->
      Spl.add_constraint simplex (Spl.Constraint.geq v n) 0 ~on_propagate
    | Step.S_gt (v,n) ->
      Spl.add_constraint simplex (Spl.Constraint.gt v n) 0 ~on_propagate
    | Step.S_define (x,le) ->
      Spl.define simplex x le
  end

let add_steps ?(f=fun()->()) (simplex:Spl.t) l : unit =
  f();
  List.iter
    (fun s -> add_step simplex s; f())
    l

(* is this simplex's state sat? *)
let check_simplex_is_sat simplex : bool =
  (try Spl.check_exn ~on_propagate simplex; true
   with Spl.E_unsat _ -> false)

(* is this problem sat? *)
let check_pb_is_sat pb : bool =
  let simplex = Spl.create() in
  (try add_steps simplex pb; Spl.check_exn ~on_propagate simplex; true
   with Spl.E_unsat _ -> false)

let check_steps l : bool =
  let simplex = Spl.create () in
  try add_steps simplex l; Spl.check_exn ~on_propagate simplex; true
  with _ -> false

(* basic debug printer for Q.t *)
let q_dbg q = Fmt.asprintf "%.3f" (Q.to_float q)

let prop_sound ?(inv=false) pb =
  let simplex = Spl.create () in
  begin match
      add_steps simplex pb;
      Spl.check ~on_propagate simplex
    with
    | Sat subst ->

      let get_val v =
        try Spl.V_map.find v subst
        with Not_found -> assert false
      in

      let check_step s =
        (try
           if inv then Spl._check_invariants simplex;
           match s with
           | Step.S_new_var _ -> ()
           | Step.S_define (x, le) ->
             let v_x = get_val x in
             let v_le =
               List.fold_left (fun s (n,y) -> Q.(s + n * get_val y)) Q.zero le
             in
             if Q.(v_x <> v_le) then (
               failwith (spf "bad def (X_%d): val(x)=%s, val(expr)=%s" x (q_dbg v_x)(q_dbg v_le))
             );
           | Step.S_lt (x, n) ->
             let v_x = get_val x in
             if Q.(v_x >= n) then failwith (spf "val=%s, n=%s"(q_dbg v_x)(q_dbg n))
           | Step.S_leq (x, n) ->
             let v_x = get_val x in
             if Q.(v_x > n) then failwith (spf "val=%s, n=%s"(q_dbg v_x)(q_dbg n))
           | Step.S_gt (x, n) ->
             let v_x = get_val x in
             if Q.(v_x <= n) then failwith (spf "val=%s, n=%s"(q_dbg v_x)(q_dbg n))
           | Step.S_geq (x, n) ->
             let v_x = get_val x in
             if Q.(v_x < n) then failwith (spf "val=%s, n=%s"(q_dbg v_x)(q_dbg n))
         with e ->
           QC.Test.fail_reportf "proof_rule failed: %a@.exn:@.%s@."
             Step.pp_ s (Printexc.to_string e)
        );
        if inv then Spl._check_invariants simplex;
        true
      in
      List.for_all check_step pb

    | Spl.Unsat cert ->
      Spl._check_cert cert;
      true
    | exception Spl.E_unsat _cert ->
      true (* TODO : check certificate *)
  end

(* a bunch of useful stats for a problem *)
let steps_stats = [
  "n-define", Step.(List.fold_left (fun n -> function S_define _ -> n+1 | _->n) 0);
  "n-bnd",
  Step.(List.fold_left
          (fun n -> function (S_leq _ | S_lt _ | S_geq _ | S_gt _) -> n+1 | _->n) 0);
  "n-vars",
  Step.(List.fold_left
          (fun n -> function S_define _ | S_new_var _ -> n+1 | _ -> n) 0);
]

let enable_stats =
  match Sys.getenv_opt "TEST_STAT" with Some("1"|"true") -> true | _ -> false

let set_stats_maybe ar =
  if enable_stats then QC.set_stats steps_stats ar else ar

let check_sound =
  let ar =
    Step.(rand_for 0 300)
    |> QC.set_collect (fun pb -> if check_steps pb then "sat" else "unsat")
    |> set_stats_maybe
  in
  QC.Test.make ~long_factor:10 ~count:500 ~name:"simplex2_sound" ar prop_sound

let prop_invariants pb =
  let simplex = Spl.create () in
  (try
    add_steps simplex pb ~f:(fun () -> Spl._check_invariants simplex);
    Spl.check_exn ~on_propagate simplex
   with Spl.E_unsat _ -> ());
  Spl._check_invariants simplex;
  true

let check_invariants =
  let ar =
    Step.(rand_for 0 300)
    |> QC.set_collect (fun pb -> if check_steps pb then "sat" else "unsat")
    |> set_stats_maybe
  in
  QC.Test.make
    ~long_factor:10 ~count:500 ~name:"simplex2_invariants"
    ar prop_invariants

let prop_backtrack pb =
  let simplex = Spl.create () in
  let stack = Stack.create() in
  let res = ref true in
  begin try
    List.iter
      (fun s ->
         let is_sat = check_simplex_is_sat simplex in
         Spl.push_level simplex;
         Stack.push is_sat stack;
         if not is_sat then (res := false; raise Exit);
         (try add_step simplex s
          with Spl.E_unsat _ -> res := false; raise Exit);
         )
    pb;
    with Exit -> ()
  end;
  res := !res && check_simplex_is_sat simplex;
  Log.debugf 50 (fun k->k "res=%b, expected=%b" !res (check_pb_is_sat pb));
  assert CCBool.(equal !res (check_pb_is_sat pb));
  (* now backtrack and check at each level *)
  while not (Stack.is_empty stack) do
    let res = Stack.pop stack in
    Spl.pop_levels simplex 1;
    assert CCBool.(equal res (check_simplex_is_sat simplex))
  done;
  true

let check_backtrack =
  let ar =
    Step.(rand_for 0 300)
    |> QC.set_collect (fun pb -> if check_steps pb then "sat" else "unsat")
    |> set_stats_maybe
  in
  QC.Test.make
    ~long_factor:10 ~count:200 ~name:"simplex2_backtrack"
    ar prop_backtrack

let check_scalable =
  let prop pb =
    let simplex = Spl.create () in
    (try
      add_steps simplex pb;
      Spl.check_exn ~on_propagate simplex
     with _ -> ());
    true
  in
  let ar =
    Step.(rand_for 3_000 5_000)
    |> QC.set_collect (fun pb -> if check_steps pb then "sat" else "unsat")
    |> set_stats_maybe
  in
  QC.Test.make ~long_factor:2 ~count:10 ~name:"simplex2_scalable"
     ar prop

let props = [
  check_invariants;
  check_sound;
  check_backtrack;
  check_scalable;
]

(* regression tests *)

module Reg = struct
  let alco_mk name f = name, `Quick, f

  let reg_prop_sound ?inv name l =
    alco_mk name @@ fun () ->
    if not (prop_sound ?inv l) then Alcotest.fail "fail";
    ()

  let reg_prop_invariants name l =
    alco_mk name @@ fun () ->
    if not (prop_invariants l) then Alcotest.fail "fail";
    ()

  let reg_prop_backtrack name l =
    alco_mk name @@ fun () ->
    if not (prop_backtrack l) then Alcotest.fail "fail";
    ()

  open Step

  let qstr = Q.of_string

  (* regression from qcheck *)
  let t1 =
    let l = [
      S_new_var 1;
      S_gt (1, qstr "2630/16347");
      S_leq (1, qstr "26878/30189");
    ] in
    reg_prop_sound "t1" l

  let t2_snd, t2_inv =
    let l = [
      S_new_var 0; S_new_var 1; S_new_var 2;
      S_define (3, [
          (qstr "19682/2117", 1);
          (qstr "26039/15663", 0);
          (qstr "-11221/17868", 2)
        ]);
    ] in
    reg_prop_sound "t2_snd" l, reg_prop_invariants "t2_inv" l

  let t3_snd =
    let l = [
      S_new_var 0;
      S_leq (0, qstr "-4831/8384");
      S_new_var 1;
      S_new_var 3;
      S_define (4, [
          qstr "-22841/11339", 0;
          qstr "5792/491", 1;
          qstr "-48819/5089", 3;
        ]);
    ] in
    reg_prop_sound "t3" l

  let t4_snd_short =
    let l = [
      S_new_var 0; S_new_var 1; S_new_var 2;
      S_define (3, [qstr "76889/9000", 2; qstr "55017/30392", 1]);
      S_define (4, [qstr "14217/27439", 3; qstr "14334/25735", 0]);
      S_leq (1, qstr "-58451/29068");
    ] in
    reg_prop_sound "t4_short" l

  let t4_snd =
    let l = [
      S_new_var 0;
      S_new_var 1;
      S_new_var 2;
      S_define (3, [
          qstr "-86184/12073", 1;
          qstr "-67593/25801", 0;
          qstr "19113/16768", 2;
        ]);
      S_define (4, [
          qstr "-26393/10015", 2;
          qstr "-12730/2099", 3
        ]);
      S_new_var 6;
      S_define (7, [
          qstr "-30739/30520", 6;
          qstr "-1840/2773", 4;
          qstr "40708/16579", 0;
          qstr "-77011/34083", 3;
        ]);
      S_leq (7, qstr "-6555/1838")
    ] in
    reg_prop_sound "t4" l

  let t5 =
    let l = [
      S_new_var 0;
      S_lt (0, qstr "-45822/1835");
      S_new_var 2;
      S_new_var 4;
      S_define (5, [qstr "40461/27377", 2; qstr"4292/31193", 0]);
      S_define (6, [qstr "-51582/5441", 5; qstr"-88432/27939", 4]);
    ] in
    reg_prop_sound "t5" l

  let t6 =
    let l = [
      S_new_var 0;
      S_new_var 1;
      S_define (3, [qstr "-21185/6058", 0; qstr "35055/29267", 1]);
      S_define (4 , [qstr "4013/2790", 1; qstr "-23314/11713", 3]);
      S_define (5 , [qstr "-15503/1523", 1; qstr "49580/15623", 0]);
      S_define (13, [qstr "41722/2083", 0; qstr "-20558/8483", 5]);
      S_define (15, [qstr "-18908/11213", 4; qstr "-66053/8560", 3]);
      S_leq (13, qstr "-5123/16411");
      S_lt (15, qstr "-9588/859");
    ] in
    reg_prop_sound ~inv:true "t6" l

  let t7 =
    let l = [
      S_new_var 1;
      S_leq (1, qstr "32908/13565");
      S_gt (1, qstr "92197/15966");
    ] in
    reg_prop_backtrack "t7" l

  (* regression for simplex certificate checking *)
  let t8 =
    let l = [
      S_new_var 0;
      S_lt (0, qstr "-8675/8802");
      S_new_var 5;
      S_define (7, [qstr "95221/14629", 5; qstr "60092/7011", 0]);
      S_lt (5, qstr "-80423/7787");
      S_geq (7, qstr "-10544/35599");
    ] in
    reg_prop_sound "t8" l

  let tests = [
    t1; t2_snd; t2_inv; t3_snd; t4_snd_short; t4_snd; t5; t6; t7; t8;
  ]
end

let tests =
  "simplex", List.flatten [ Reg.tests ]
