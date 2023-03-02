module T = Sidekick_core_logic.Term
module Level = Sidekick_core_logic.Level

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
    | O_level lvl -> Level.pp out lvl
    | O_name n -> Fmt.fprintf out "#name %S" n
    | O_term t -> T.pp_debug out t
    | O_ind (n, _) -> Fmt.fprintf out "#ind %s" n

  let dummy : t = O_name ""
end

(** Map indexes to objects *)
module Idx = struct
  type t = { obj: obj Vec.t }

  (* create. The slot 0 is already filled with name "" *)
  let create () : t = { obj = Vec.make 1 Obj.dummy }

  (** ensure that index [n] is valid *)
  let ensure_size (self : t) (n : int) : unit =
    if n >= Vec.size self.obj then Vec.ensure_size self.obj ~elt:Obj.dummy n

  let[@inline] get (self : t) (i : int) : obj = Vec.get self.obj i

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
end

(** Join two names with "." *)
let name_join a b =
  if a = "" then
    b
  else
    a ^ "." ^ b

let process_files (files : string list) : unit =
  let start = Mtime_clock.now () in
  let st = T.Store.create ~size:1024 () in
  Log.debugf 1 (fun k ->
      k "(@[process-files %a@])" Fmt.Dump.(list string) files);

  let n_lines = ref 0 in

  let proc_file (file : string) : unit =
    let@ ic = CCIO.with_in file in
    let idx = Idx.create () in

    Parse.parse (`In ic)
      (module struct
        let line _ = incr n_lines
        let ns ~at i s = Idx.set_name idx at (name_join (Idx.get_name idx i) s)

        let ni ~at i n =
          Idx.set_name idx at (name_join (Idx.get_name idx i) (string_of_int n))
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
  let opts =
    [
      "--debug", Arg.Int Log.set_debug, " set debug level";
      "-d", Arg.Int Log.set_debug, " like --debug";
    ]
    |> Arg.align
  in

  Arg.parse opts (CCList.Ref.push files) "leancheck file+";
  if !files = [] then failwith "provide at least one file";

  process_files (List.rev !files)
