
(** {1 simple sudoku solver} *)

module Fmt = CCFormat
module Vec = Sidekick_util.Vec
module Log = Sidekick_util.Log

module Profile = Sidekick_util.Profile

let errorf msg = Fmt.kasprintf failwith msg

module Cell : sig
  type t = private int
  val equal : t -> t -> bool
  val neq : t -> t -> bool
  val hash : t -> int
  val empty : t
  val is_empty : t -> bool
  val is_full : t -> bool
  val make : int -> t
  val pp : t Fmt.printer
end = struct
  type t = int
  let empty = 0
  let[@inline] make i = assert (i >= 0 && i <= 9); i
  let[@inline] is_empty x = x = 0
  let[@inline] is_full x = x > 0
  let hash = CCHash.int
  let[@inline] equal (a:t) b = a=b
  let[@inline] neq (a:t) b = a<>b
  let pp out i = if i=0 then Fmt.char out '.' else Fmt.int out i
end

module Grid : sig
  type t

  val get : t -> int -> int -> Cell.t
  val set : t -> int -> int -> Cell.t -> t

  (** A set of related cells *)
  type set = (int*int*Cell.t) Iter.t

  val rows : t -> set Iter.t
  val cols : t -> set Iter.t
  val squares : t -> set Iter.t

  val all_cells : t -> (int*int*Cell.t) Iter.t

  val parse : string -> t
  val is_full : t -> bool
  val is_valid : t -> bool
  val matches : pat:t -> t -> bool
  val pp : t Fmt.printer
end = struct
  type t = Cell.t array

  let[@inline] get (s:t) i j = s.(i*9 + j)

  let[@inline] set (s:t) i j n =
    let s' = Array.copy s in
    s'.(i*9 + j) <- n;
    s'

  (** A set of related cells *)
  type set = (int*int*Cell.t) Iter.t

  open Iter.Infix

  let all_cells (g:t) =
    0 -- 8 >>= fun i ->
    0 -- 8 >|= fun j -> (i,j,get g i j)

  let rows (g:t) =
    0 -- 8 >|= fun i ->
    ( 0 -- 8 >|= fun j -> (i,j,get g i j))

  let cols g =
    0 -- 8 >|= fun j ->
    ( 0 -- 8 >|= fun i -> (i,j,get g i j))

  let squares g =
    0 -- 2 >>= fun sq_i ->
    0 -- 2 >|= fun sq_j ->
    ( 0 -- 2 >>= fun off_i ->
      0 -- 2 >|= fun off_j ->
      let i = 3*sq_i + off_i in
      let j = 3*sq_j + off_j in
      (i,j,get g i j))

  let is_full g = Array.for_all Cell.is_full g

  let is_valid g =
    let all_distinct (s:set) =
      (s >|= fun (_,_,c) -> c)
      |> Iter.diagonal
      |> Iter.for_all (fun (c1,c2) -> Cell.neq c1 c2)
    in
    Iter.for_all all_distinct @@ rows g &&
    Iter.for_all all_distinct @@ cols g &&
    Iter.for_all all_distinct @@ squares g

  let matches ~pat:g1 g2 : bool =
    all_cells g1
    |> Iter.filter (fun (_,_,c) -> Cell.is_full c)
    |> Iter.for_all (fun (x,y,c) -> Cell.equal c @@ get g2 x y)

  let pp out g =
    Fmt.fprintf out "@[<v>";
    Array.iteri
      (fun i n ->
         Cell.pp out n;
         if i mod 9 = 8 then Fmt.fprintf out "@,")
      g;
    Fmt.fprintf out "@]"

  let parse (s:string) : t =
    if String.length s < 81 then (
      errorf "line is too short, expected 81 chars, not %d" (String.length s);
    );
    let a = Array.make 81 Cell.empty in
    for i = 0 to 80 do
      let c = String.get s i in
      let n = if c = '.' then 0 else Char.code c - Char.code '0' in
      if n < 0 || n > 9 then errorf "invalid char %c" c;
      a.(i) <- Cell.make n
    done;
    a
end

module B_ref = Sidekick_util.Backtrackable_ref

module Solver : sig
  type t
  val create : Grid.t -> t
  val solve : t -> Grid.t option
end = struct
  open Sidekick_sat.Solver_intf

  (* formulas *)
  module F = struct
    type t = bool*int*int*Cell.t
    let equal (sign1,x1,y1,c1)(sign2,x2,y2,c2) =
      sign1=sign2 && x1=x2 && y1=y2 && Cell.equal c1 c2
    let hash (sign,x,y,c) = CCHash.(combine4 (bool sign)(int x)(int y)(Cell.hash c))
    let pp out (sign,x,y,c) =
      Fmt.fprintf out "[@[(%d,%d) %s %a@]]" x y (if sign then "=" else "!=") Cell.pp c
    let neg (sign,x,y,c) = (not sign,x,y,c)
    let norm_sign ((sign,_,_,_) as f) = if sign then f, true else neg f, false

    let make sign x y (c:Cell.t) : t = (sign,x,y,c)
  end

  type lit = F.t

  module Theory = struct
    type proof = unit
    type proof_step = unit
    module Lit = F
    type lit = Lit.t
    module Proof = Sidekick_sat.Proof_dummy.Make(Lit)
    type t = {
      grid: Grid.t B_ref.t;
    }

    let create g : t = {grid=B_ref.create g}
    let[@inline] grid self : Grid.t = B_ref.get self.grid
    let[@inline] set_grid self g : unit = B_ref.set self.grid g

    let push_level self = B_ref.push_level self.grid
    let pop_levels self n = B_ref.pop_levels self.grid n

    let pp_c_ = Fmt.(list ~sep:(return "@ ∨ ")) F.pp
    let[@inline] logs_conflict kind c : unit =
      Log.debugf 4 (fun k->k "(@[conflict.%s@ %a@])" kind pp_c_ c)

    (* check that all cells are full *)
    let check_full_ (self:t) (acts:(Lit.t,proof,proof_step) acts) : unit =
      Profile.with_ "check-full" @@ fun () ->
      let (module A) = acts in
      Grid.all_cells (grid self)
        (fun (x,y,c) ->
           if Cell.is_empty c then (
             let c =
               CCList.init 9
                 (fun c -> F.make true x y (Cell.make (c+1)))
             in
             Log.debugf 4 (fun k->k "(@[add-clause@ %a@])" pp_c_ c);
             A.add_clause ~keep:true c ();
           ))

    (* check constraints *)
    let check_ (self:t) (acts:(Lit.t,proof,proof_step) acts) : unit =
      Profile.with_ "check-constraints" @@ fun () ->
      Log.debugf 4 (fun k->k "(@[sudoku.check@ @[:g %a@]@])" Grid.pp (B_ref.get self.grid));
      let (module A) = acts in
      let[@inline] all_diff kind f =
        let pairs =
          f (grid self)
          |> Iter.flat_map
            (fun set ->
               set
               |> Iter.filter (fun (_,_,c) -> Cell.is_full c)
               |> Iter.diagonal)
        in
        pairs
          (fun ((x1,y1,c1),(x2,y2,c2)) ->
             if Cell.equal c1 c2 then (
               assert (x1<>x2 || y1<>y2);
               let c = [F.make false x1 y1 c1; F.make false x2 y2 c2] in
               logs_conflict ("all-diff." ^ kind) c;
               A.raise_conflict c ()
             ))
      in
      all_diff "rows" Grid.rows;
      all_diff "cols" Grid.cols;
      all_diff "squares" Grid.squares;
      ()

    let trail_ (acts:(Lit.t,proof,proof_step) acts) =
      let (module A) = acts in
      A.iter_assumptions

    (* update current grid with the given slice *)
    let add_slice (self:t) (acts:(Lit.t,proof,proof_step) acts) : unit =
      let (module A) = acts in
      trail_ acts
        (function
          | false,_,_,_ -> ()
          | true,x,y,c ->
            assert (Cell.is_full c);
            let grid = grid self in
            let c' = Grid.get grid x y in
            if Cell.is_empty c' then (
              set_grid self (Grid.set grid x y c);
            ) else if Cell.neq c c' then (
              (* conflict: at most one value *)
              let c = [F.make false x y c; F.make false x y c'] in
              logs_conflict "at-most-one" c;
              A.raise_conflict c ()
            )
        )

    let partial_check (self:t) acts : unit =
      Profile.with_ "partial-check" @@ fun () ->
      Log.debugf 4
        (fun k->k "(@[sudoku.partial-check@ :trail [@[%a@]]@])"
            (Fmt.list F.pp) (trail_ acts |> Iter.to_list));
      add_slice self acts;
      check_ self acts

    let final_check (self:t) acts : unit =
      Profile.with_ "final-check" @@ fun () ->
      Log.debugf 4 (fun k->k "(@[sudoku.final-check@])");
      check_full_ self acts;
      check_ self acts

  end

  module S = Sidekick_sat.Make_cdcl_t(Theory)

  type t = {
    grid0: Grid.t;
    solver: S.t;
  }

  let solve (self:t) : _ option =
    Profile.with_ "sudoku.solve" @@ fun () ->
    let assumptions =
      Grid.all_cells self.grid0
      |> Iter.filter (fun (_,_,c) -> Cell.is_full c)
      |> Iter.map (fun (x,y,c) -> F.make true x y c)
      |> Iter.to_rev_list
    in
    Log.debugf 2
      (fun k->k "(@[sudoku.solve@ :assumptions %a@])" (Fmt.Dump.list F.pp) assumptions);
    let r =
      match S.solve self.solver ~assumptions with
      | S.Sat _ -> Some (Theory.grid (S.theory self.solver))
      | S.Unsat _ -> None
    in
    (* TODO: print some stats *)
    r

  let create g : t =
    { solver=S.create ~proof:() (Theory.create g); grid0=g }
end

let solve_grid (g:Grid.t) : Grid.t option =
  let s = Solver.create g in
  Solver.solve s

module type CHRONO = sig
  val pp_elapsed : Fmt.formatter -> unit
end

let chrono ~pp_time : (module CHRONO) =
  let module M = struct
    let start = Sys.time()
    let pp_elapsed out =
      if pp_time then
        Fmt.fprintf out " (in %.3fs)" (Sys.time() -. start)
  end in
  (module M)

let solve_file ~pp_time file =
  Profile.with_ "solve-file" @@ fun () ->
  let open (val chrono ~pp_time) in
  Format.printf "solve grids in file %S@." file;

  let grids =
    CCIO.with_in file CCIO.read_lines_l
    |> CCList.filter_map
      (fun s ->
         let s = String.trim s in
         if s="" then None
         else match Grid.parse s with
           | g -> Some g
           | exception e ->
             errorf "cannot parse sudoku %S: %s@." s (Printexc.to_string e))
  in
  Format.printf "parsed %d grids%t@." (List.length grids) pp_elapsed;
  List.iter
    (fun g ->
       Format.printf "@[<v>@,#########################@,@[<2>solve grid:@ %a@]@]@." Grid.pp g;
       let open (val chrono ~pp_time) in
       match solve_grid g with
       | None -> Format.printf "no solution%t@." pp_elapsed
       | Some g' when not @@ Grid.is_full g' ->
         errorf "grid %a@ is not full" Grid.pp g'
       | Some g' when not @@ Grid.is_valid g' ->
         errorf "grid %a@ is not valid" Grid.pp g'
       | Some g' when not @@ Grid.matches ~pat:g g' ->
         errorf "grid %a@ @[<2>does not match original@ %a@]" Grid.pp g' Grid.pp g
       | Some g' ->
         Format.printf "@[<v>@[<2>solution%t:@ %a@]@,###################@]@."
           pp_elapsed Grid.pp g')
    grids;
  Format.printf "@.solved %d grids%t@." (List.length grids) pp_elapsed;
  ()

let () =
  Sidekick_tef.with_setup @@ fun () ->

  Fmt.set_color_default true;
  let files = ref [] in
  let debug = ref 0 in
  let pp_time = ref true in
  let opts = [
    "--debug", Arg.Set_int debug, " debug";
    "-d", Arg.Set_int debug, " debug";
    "--no-time", Arg.Clear pp_time, " do not print solve time";
  ] |> Arg.align in
  Arg.parse opts (fun f -> files := f :: !files) "sudoku_solve [options] <file>";
  Log.set_debug !debug;
  try
    List.iter (fun f -> solve_file ~pp_time:!pp_time f) !files;
  with
  | Failure msg | Invalid_argument msg ->
    Format.printf "@{<Red>Error@}:@.%s@." msg;
    exit 1
