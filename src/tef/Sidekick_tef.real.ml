module P = Sidekick_util.Profile

let active =
  lazy
    (match Sys.getenv "TRACE" with
    | "1" | "true" -> true
    | _ -> false
    | exception Not_found -> false)

let program_start = Mtime_clock.now ()

module Make () : P.BACKEND = struct
  let first_ = ref true
  let closed_ = ref false

  let teardown_ oc =
    if not !closed_ then (
      closed_ := true;
      output_char oc ']';
      (* close array *)
      flush oc;
      close_out_noerr oc
    )

  (* connection to subprocess writing into the file *)
  let oc =
    let oc = open_out_bin "trace.json" in
    output_char oc '[';
    at_exit (fun () -> teardown_ oc);
    oc

  let get_ts () : float =
    let now = Mtime_clock.now () in
    Mtime.Span.to_us (Mtime.span program_start now)

  let emit_sep_ () =
    if !first_ then
      first_ := false
    else
      output_string oc ",\n"

  let char = output_char
  let raw_string = output_string
  let int oc i = Printf.fprintf oc "%d" i

  let str_val oc (s : string) =
    char oc '"';
    let encode_char c =
      match c with
      | '"' -> raw_string oc {|\"|}
      | '\\' -> raw_string oc {|\\|}
      | '\n' -> raw_string oc {|\n|}
      | '\b' -> raw_string oc {|\b|}
      | '\r' -> raw_string oc {|\r|}
      | '\t' -> raw_string oc {|\t|}
      | _ when Char.code c <= 0x1f ->
        raw_string oc {|\u00|};
        Printf.fprintf oc "%02x" (Char.code c)
      | c -> char oc c
    in
    String.iter encode_char s;
    char oc '"'

  (* emit args, if not empty. [ppv] is used to print values. *)
  let emit_args_o_ ppv oc args : unit =
    if args <> [] then (
      Printf.fprintf oc {json|,"args": {|json};
      List.iteri
        (fun i (n, value) ->
          if i > 0 then Printf.fprintf oc ",";
          Printf.fprintf oc {json|"%s":%a|json} n ppv value)
        args;
      char oc '}'
    )

  let emit_duration_event ~name ~start ~end_ ~args () : unit =
    let dur = end_ -. start in
    let ts = start in
    let pid = Unix.getpid () in
    let tid = Thread.id (Thread.self ()) in
    emit_sep_ ();
    Printf.fprintf oc
      {json|{"pid": %d,"cat":"","tid": %d,"dur": %.2f,"ts": %.2f,"name":%a,"ph":"X"%a}|json}
      pid tid dur ts str_val name (emit_args_o_ str_val) args;
    ()

  let emit_instant_event ~name ~ts ~args () : unit =
    let pid = Unix.getpid () in
    let tid = Thread.id (Thread.self ()) in
    emit_sep_ ();
    Printf.fprintf oc
      {json|{"pid": %d,"cat":"","tid": %d,"ts": %.2f,"name":%a,"ph":"I"%a}|json}
      pid tid ts str_val name (emit_args_o_ str_val) args;
    ()

  let emit_count_event ~name ~ts (cs : _ list) : unit =
    let pid = Unix.getpid () in
    let tid = Thread.id (Thread.self ()) in
    emit_sep_ ();
    Printf.fprintf oc
      {json|{"pid": %d,"cat":"","tid": %d,"ts": %.2f,"name":%a,"ph":"C"%a}|json}
      pid tid ts str_val name (emit_args_o_ int) cs;
    ()

  let teardown () = teardown_ oc
end

let setup_ =
  lazy
    (let (lazy active) = active in
     let b =
       if active then
         Some (module Make () : P.BACKEND)
       else
         None
     in
     P.Control.setup b)

let setup () = Lazy.force setup_
let teardown = P.Control.teardown

let[@inline] with_setup f =
  setup ();
  try
    let x = f () in
    teardown ();
    x
  with e ->
    teardown ();
    raise e
