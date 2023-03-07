module T = Sidekick_cic_lib.Term
module Const = Sidekick_cic_lib.Const
module Level = Sidekick_cic_lib.Level

let ( let@ ) = ( @@ )

(** Map indexes to objects *)
module Idx = struct
  type t = { names: string Vec.t; levels: Level.t Vec.t; terms: T.t Vec.t }

  (* create. The slot 0 is already filled with name "" *)
  let create () : t =
    let names = Vec.create () in
    Vec.push names "";
    let levels = Vec.create () in
    let terms = Vec.create () in
    { names; levels; terms }

  (** ensure that index [n] is valid *)
  let ensure_size (v : _ Vec.t) ~dummy (n : int) : unit =
    if n >= Vec.size v then Vec.ensure_size v ~elt:dummy n

  let set_name self i n : unit =
    ensure_size self.names ~dummy:"" (i + 1);
    Vec.set self.names i n

  let get_name self i : string =
    match Vec.get self.names i with
    | s -> s
    | exception _ -> Error.errorf "invalid name at %d" i

  let set_term self i t : unit =
    ensure_size self.terms ~dummy:T.type_ (i + 1);
    Vec.set self.terms i t

  let get_term self i : T.t =
    match Vec.get self.terms i with
    | s -> s
    | exception _ -> Error.errorf "invalid term at %d" i

  let set_level self i l : unit =
    ensure_size self.levels ~dummy:Level.zero (i + 1);
    Vec.set self.levels i l

  let get_level self i : Level.t =
    match Vec.get self.levels i with
    | s -> s
    | exception _ -> Error.errorf "invalid level at %d" i

  let dump out (self : t) : unit =
    let pp_with_idx ppx out (i, x) = Fmt.fprintf out "[%d]=%a" i ppx x in
    Fmt.fprintf out
      "(@[idx {@ names: [@[%a@]],@ terms: [@[%a@]],@ levels: [@[%a@]]}@])"
      (Fmt.iter ~sep:(Fmt.return ";@ ") (pp_with_idx Fmt.Dump.string))
      (Vec.to_iter self.names |> Iter.zip_i)
      (Fmt.iter ~sep:(Fmt.return ";@ ") (pp_with_idx T.pp_debug))
      (Vec.to_iter self.terms |> Iter.zip_i)
      (Fmt.iter ~sep:(Fmt.return ";@ ") Level.pp)
      (Vec.to_iter self.levels)
end

(** Join two names with "." *)
let name_join a b =
  if a = "" then
    b
  else
    a ^ "." ^ b

let binder_of_string = function
  | "#BD" -> T.BD
  | "#BI" -> T.BI
  | "#BS" -> T.BS
  | "#BC" -> T.BC
  | s -> failwith (Printf.sprintf "invalid binder: %S" s)

let process_files ~max_err (files : string list) : unit =
  let start = Mtime_clock.now () in

  Log.debugf 1 (fun k ->
      k "(@[process-files %a@])" Fmt.Dump.(list string) files);

  let n_lines = ref 0 in

  (* get a level. 0 means level 0. *)
  let get_level idx i =
    if i = 0 then
      Level.zero
    else
      Idx.get_level idx i
  in

  let proc_file (file : string) : unit =
    let@ ic = CCIO.with_in file in
    let idx = Idx.create () in

    Parse.parse ~max_errors:max_err (`In ic)
      (module struct
        let line _ = incr n_lines

        let ns ~at i s : unit =
          Idx.set_name idx at (name_join (Idx.get_name idx i) s)

        let ni ~at i n : unit =
          Idx.set_name idx at (name_join (Idx.get_name idx i) (string_of_int n))

        let us ~at i : unit =
          Idx.set_level idx at (Level.succ @@ get_level idx i)

        let um ~at i j : unit =
          Idx.set_level idx at (Level.max (get_level idx i) (get_level idx j))

        let uim ~at i j : unit =
          Idx.set_level idx at (Level.imax (get_level idx i) (get_level idx j))

        let up ~at i : unit =
          Idx.set_level idx at (Level.var @@ Idx.get_name idx i)

        let ev ~at i : unit = Idx.set_term idx at (T.bvar_i i)

        let ea ~at i j : unit =
          Idx.set_term idx at (T.app (Idx.get_term idx i) (Idx.get_term idx j))

        let ec ~at i_name i_args : unit =
          let name = Idx.get_name idx i_name in
          let args = List.map (Idx.get_level idx) i_args in
          Idx.set_term idx at (T.const (Const.make name) args)

        let es ~at i : unit =
          Idx.set_term idx at (T.type_of_univ (Idx.get_level idx i))

        let el ~at b n i j : unit =
          Idx.set_term idx at
            (T.lam (binder_of_string b) (Idx.get_name idx n)
               ~var_ty:(Idx.get_term idx i) (Idx.get_term idx j))

        let ep ~at b n i j : unit =
          Idx.set_term idx at
            (T.pi (binder_of_string b) (Idx.get_name idx n)
               ~var_ty:(Idx.get_term idx i) (Idx.get_term idx j))

        let after_line () = Fmt.eprintf "%a@." Idx.dump idx
      end)
  in

  List.iter proc_file files;

  let elapsed =
    (Mtime.span (Mtime_clock.now ()) start |> Mtime.Span.to_float_ns) /. 1e9
  in
  Log.debugf 1 (fun k ->
      k "number of lines processed: %d in %.4fs (%.2f/s)" !n_lines elapsed
        (float !n_lines /. elapsed));
  ()

let () =
  let files = ref [] in
  let max_err = ref max_int in
  let opts =
    [
      "--debug", Arg.Int Log.set_debug, " set debug level";
      "-d", Arg.Int Log.set_debug, " like --debug";
      ( "--max-err",
        Arg.Set_int max_err,
        " maximum number of errors before bailing out" );
      ( "-c",
        Arg.Unit (fun () -> CCFormat.set_color_default true),
        " enable colors" );
      ( "-nc",
        Arg.Unit (fun () -> CCFormat.set_color_default false),
        " disable colors" );
    ]
    |> Arg.align
  in

  Arg.parse opts (CCList.Ref.push files) "leancheck file+";
  if !files = [] then failwith "provide at least one file";

  process_files ~max_err:!max_err (List.rev !files)
