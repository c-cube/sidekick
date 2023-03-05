module T = Sidekick_cic_lib.Term
module Level = Sidekick_cic_lib.Level

let ( let@ ) = ( @@ )

type obj =
  | O_level of Level.t
  | O_name of string
  | O_term of T.t
  | O_ind of string * T.t

(** Intermediate objects in a proof *)
module Obj = struct
  type t = obj

  let pp out = function
    | O_level lvl -> Fmt.fprintf out "(#lvl %a)" Level.pp lvl
    | O_name n -> Fmt.fprintf out "(#name %S)" n
    | O_term t -> T.pp_debug out t
    | O_ind (n, _) -> Fmt.fprintf out "(#ind %s)" n

  let dummy : t = O_name ""
end

(** Map indexes to objects *)
module Idx = struct
  type t = { obj: obj Vec.t }

  (* create. The slot 0 is already filled with name "" *)
  let create () : t =
    let obj = Vec.create () in
    Vec.push obj Obj.dummy;
    { obj }

  (** ensure that index [n] is valid *)
  let ensure_size (self : t) (n : int) : unit =
    if n >= Vec.size self.obj then Vec.ensure_size self.obj ~elt:Obj.dummy n

  let[@inline] get (self : t) (i : int) : obj =
    try Vec.get self.obj i
    with _ -> Error.errorf "cannot access object at index %d" i

  let[@inline] set (self : t) (i : int) o : unit =
    ensure_size self i;
    Vec.set self.obj i o

  let[@inline] set_name self i n : unit = set self i (O_name n)
  let[@inline] set_level self i l : unit = set self i (O_level l)
  let[@inline] set_term self i t : unit = set self i (O_term t)

  let get_name self i : string =
    match get self i with
    | O_name s -> s
    | _o -> Error.errorf "expected a name at %d, got %a" i Obj.pp _o

  let get_level self i : Level.t =
    match get self i with
    | O_level l -> l
    | _o -> Error.errorf "expected a level at %d, got %a" i Obj.pp _o

  let get_term self i : T.t =
    match get self i with
    | O_term t -> t
    | _o -> Error.errorf "expected a term at %d, got %a" i Obj.pp _o

  let dump out (self : t) : unit =
    Fmt.fprintf out "(@[idx %a@])"
      (Fmt.iter ~sep:(Fmt.return "@ ") Obj.pp)
      (Vec.to_iter self.obj)
end

(** Join two names with "." *)
let name_join a b =
  if a = "" then
    b
  else
    a ^ "." ^ b

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
    ]
    |> Arg.align
  in

  Arg.parse opts (CCList.Ref.push files) "leancheck file+";
  if !files = [] then failwith "provide at least one file";

  process_files ~max_err:!max_err (List.rev !files)
