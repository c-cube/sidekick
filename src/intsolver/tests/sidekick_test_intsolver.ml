
open CCMonomorphic

module Fmt = CCFormat
module QC = QCheck
module Log = Sidekick_util.Log
let spf = Printf.sprintf

module ZarithZ = Z
module Z = Sidekick_zarith.Int

module Var = struct
  include CCInt

  let pp out x = Format.fprintf out "X_%d" x

  let rand n : t QC.arbitrary = QC.make ~print:(Fmt.to_string pp) @@ QC.Gen.(0--n)
  type lit = int
  let pp_lit = Fmt.int
  let not_lit i = Some (- i)
end

module Var_map = CCMap.Make(Var)

module Solver = Sidekick_intsolver.Make(struct
    module Z = Z
    type term = Var.t
    let pp_term = Var.pp
    type lit = Var.lit
    let pp_lit = Var.pp_lit
    module T_map = Var_map
  end)

let unwrap_opt_ msg = function
  | Some x -> x
  | None -> failwith msg

let rand_n low n : Z.t QC.arbitrary =
  QC.map ~rev:ZarithZ.to_int Z.of_int QC.(low -- n)

(* TODO: fudge *)
let rand_z = rand_n (-15) 15

module Step = struct
  module G = QC.Gen

  type linexp = (Z.t * Var.t) list

  type t =
    | S_new_var of Var.t
    | S_define of Var.t * (Z.t * Var.t) list
    | S_leq of linexp * Z.t
    | S_lt of linexp * Z.t
    | S_eq of linexp * Z.t

  let pp_le out (le:linexp) =
    let pp_pair out (n,x) =
      if Z.equal Z.one n then Var.pp out x
      else Fmt.fprintf out "%a . %a" Z.pp n Var.pp x in
    Fmt.fprintf out "(@[%a@])"
      Fmt.(list ~sep:(return " +@ ") pp_pair) le

  let pp_ out = function
    | S_new_var v -> Fmt.fprintf out "(@[new-var %a@])" Var.pp v
    | S_define (v,le) -> Fmt.fprintf out "(@[define %a@ := %a@])" Var.pp v pp_le le
    | S_leq (le,n) -> Fmt.fprintf out "(@[upper %a <= %a@])" pp_le le Z.pp n
    | S_lt (le,n) -> Fmt.fprintf out "(@[upper %a < %a@])" pp_le le Z.pp n
    | S_eq (le,n) -> Fmt.fprintf out "(@[lower %a > %a@])" pp_le le Z.pp n

  (* check that a sequence is well formed *)
  let well_formed (l:t list) : bool =
    let rec aux vars = function
      | [] -> true
      | S_new_var v :: tl ->
        not (List.mem v vars) && aux (v::vars) tl
      | (S_leq (le,_) | S_lt (le,_) | S_eq (le,_)) :: tl ->
        List.for_all (fun (_,x) -> List.mem x vars) le && aux vars tl
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
    | S_leq _ | S_lt _ | S_eq _ -> QC.Iter.empty
    | S_define (x, le) ->
      let open QC.Iter in
      let* le = S.list le in
      if List.length le >= 2 then return (S_define (x,le)) else empty

  let rand_steps (n:int) : t list QC.Gen.t =
    let open G in
    let rec aux n vars acc =
      if n<=0 then return (List.rev acc)
      else (
        let gen_linexp =
          let* vars' = G.shuffle_l vars in
          let* n = 1 -- (min 7 @@ List.length vars') in
          let vars' = CCList.take n vars' in
          assert (List.length vars' = n);
          let* coeffs = list_repeat n rand_z.gen in
          return (List.combine coeffs vars')
        in
        let* vars, proof_rule =
          frequency @@ List.flatten [
            (* add a constraint *)
            (match vars with
             | [] -> []
             | _ ->
               let gen =
                 let+ le = gen_linexp
                 and+ kind = frequencyl [5, `Leq; 5, `Lt; 3,`Eq]
                 and+ n = rand_z.QC.gen in
                 vars, (match kind with
                     | `Lt -> S_lt(le,n)
                     | `Leq -> S_leq(le,n)
                     | `Eq -> S_eq(le,n)
                   )
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
                 let+ le = gen_linexp in
                 v::vars, S_define (v, le)
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

  let rand : t list QC.arbitrary = rand_for 1 15
end

let on_propagate _ ~reason:_ = ()

(* add a single proof_rule to the solvere *)
let add_step solver (s:Step.t) : unit =
  begin match s with
    | Step.S_new_var _v -> ()
    | Step.S_leq (le,n) ->
      Solver.assert_ solver le Solver.Op.Leq n ~lit:0
    | Step.S_lt (le,n) ->
      Solver.assert_ solver le Solver.Op.Lt n ~lit:0
    | Step.S_eq (le,n) ->
      Solver.assert_ solver le Solver.Op.Eq n ~lit:0
    | Step.S_define (x,le) ->
      Solver.define solver x le
  end

let add_steps ?(f=fun()->()) (solver:Solver.t) l : unit =
  f();
  List.iter
    (fun s -> add_step solver s; f())
    l

(* is this solver's state sat? *)
let check_solver_is_sat solver : bool =
  match Solver.check solver with
  | Solver.Sat _ -> true
  | Solver.Unsat _ -> false

(* is this problem sat? *)
let check_pb_is_sat pb : bool =
  let solver = Solver.create() in
  add_steps solver pb;
  check_solver_is_sat solver

(* basic debug printer for Q.t *)
let str_z n = ZarithZ.to_string n

let prop_sound ?(inv=false) pb =
  let solver = Solver.create () in
  begin match
      add_steps solver pb;
      Solver.check solver
    with
    | Sat model ->

      let get_val v =
        match Solver.Model.eval model v with
        | Some n -> n
        | None -> assert false
      in

      let eval_le le =
        List.fold_left (fun s (n,y) -> Z.(s + n * get_val y)) Z.zero le
      in

      let check_step s =
        (try
           if inv then Solver._check_invariants solver;
           match s with
           | Step.S_new_var _ -> ()
           | Step.S_define (x, le) ->
             let v_x = get_val x in
             let v_le = eval_le le in
             if Z.(v_x <> v_le) then (
               failwith (spf "bad def (X_%d): val(x)=%s, val(expr)=%s" x (str_z v_x)(str_z v_le))
             );
           | Step.S_lt (x, n) ->
             let v_x = eval_le x in
             if Z.(v_x >= n) then failwith (spf "val=%s, n=%s"(str_z v_x)(str_z n))
           | Step.S_leq (x, n) ->
             let v_x = eval_le x in
             if Z.(v_x > n) then failwith (spf "val=%s, n=%s"(str_z v_x)(str_z n))
           | Step.S_eq (x, n) ->
             let v_x = eval_le x in
             if Z.(v_x <> n) then failwith (spf "val=%s, n=%s"(str_z v_x)(str_z n))
         with e ->
           QC.Test.fail_reportf "proof_rule failed: %a@.exn:@.%s@."
             Step.pp_ s (Printexc.to_string e)
        );
        if inv then Solver._check_invariants solver;
        true
      in
      List.for_all check_step pb

    | Solver.Unsat _cert ->
      (* FIXME:
         Solver._check_cert cert;
         *)
      true
  end

(* a bunch of useful stats for a problem *)
let steps_stats = [
  "n-define", Step.(List.fold_left (fun n -> function S_define _ -> n+1 | _->n) 0);
  "n-bnd",
  Step.(List.fold_left
          (fun n -> function (S_leq _ | S_lt _ | S_eq _) -> n+1 | _->n) 0);
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
    Step.(rand_for 0 15)
    |> QC.set_collect (fun pb -> if check_pb_is_sat pb then "sat" else "unsat")
    |> set_stats_maybe
  in
  QC.Test.make ~long_factor:10 ~count:500 ~name:"solver2_sound" ar prop_sound

let prop_backtrack pb =
  let solver = Solver.create () in
  let stack = Stack.create() in
  let res = ref true in
  begin try
    List.iter
      (fun s ->
         let is_sat = check_solver_is_sat solver in
         Solver.push_level solver;
         Stack.push is_sat stack;
         if not is_sat then (res := false; raise Exit);
         add_step solver s;
      )
    pb;
    with Exit -> ()
  end;
  res := !res && check_solver_is_sat solver;
  Log.debugf 50 (fun k->k "res=%b, expected=%b" !res (check_pb_is_sat pb));
  assert CCBool.(equal !res (check_pb_is_sat pb));
  (* now backtrack and check at each level *)
  while not (Stack.is_empty stack) do
    let res = Stack.pop stack in
    Solver.pop_levels solver 1;
    assert CCBool.(equal res (check_solver_is_sat solver))
  done;
  true

let check_backtrack =
  let ar =
    Step.(rand_for 0 15)
    |> QC.set_collect (fun pb -> if check_pb_is_sat pb then "sat" else "unsat")
    |> set_stats_maybe
  in
  QC.Test.make
    ~long_factor:10 ~count:200 ~name:"solver2_backtrack"
    ar prop_backtrack

let props = [
  check_sound;
  check_backtrack;
]

(* regression tests *)

module Reg = struct
  let alco_mk name f = name, `Quick, f

  let reg_prop_sound ?inv name l =
    alco_mk name @@ fun () ->
    if not (prop_sound ?inv l) then Alcotest.fail "fail";
    ()

  let reg_prop_backtrack name l =
    alco_mk name @@ fun () ->
    if not (prop_backtrack l) then Alcotest.fail "fail";
    ()

  open Step
  let tests = [
  ]
end

let tests =
  "solver", List.flatten [ Reg.tests ]
