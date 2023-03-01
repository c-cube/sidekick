module type CALLBACK = Parse_intf.CALLBACK

type callback = (module CALLBACK)
type input = [ `String of string | `In of in_channel ]

module type IN = sig
  val next_line : unit -> string option
end

let in_of_input (i : input) : (module IN) =
  match i with
  | `String s ->
    (module struct
      let i = ref 0

      let next_line () =
        if !i = String.length s then
          None
        else (
          match String.index_from s !i '\n' with
          | exception Not_found ->
            let r = Some (String.sub s !i (String.length s - !i)) in
            i := String.length s;
            r
          | j ->
            let r = Some (String.sub s !i (j - !i)) in
            i := j + 1;
            r
        )
    end)
  | `In ic ->
    (module struct
      let next_line () = try Some (input_line ic) with End_of_file -> None
    end)

let parse (input : input) (cb : callback) : unit =
  let (module CB) = cb in
  let (module IN) = in_of_input input in

  let rec loop () =
    match IN.next_line () with
    | None -> ()
    | Some line ->
      Log.debugf 50 (fun k -> k "(leancheck.parse-line %S)" line);
      CB.line line;

      (* TODO: cb *)
      loop ()
  in

  loop ()
