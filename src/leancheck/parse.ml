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

module Lex = struct
  type token = I of int | S of string

  let lex_line (s : string) : token list =
    let l = String.split_on_char ' ' s in
    List.map
      (fun s ->
        match int_of_string_opt s with
        | None -> S s
        | Some i -> I i)
      l
end

let parse ?(max_errors = max_int) (input : input) (cb : callback) : unit =
  let (module CB) = cb in
  let (module IN) = in_of_input input in

  let n_line = ref 0 in
  let n_errors = ref 0 in

  let rec loop () =
    match IN.next_line () with
    | None -> ()
    | Some line ->
      Log.debugf 50 (fun k -> k "(leancheck.parse-line[%d] %S)" !n_line line);
      CB.line line;

      (try
         let open Lex in
         match Lex.lex_line line with
         | [ I at; S "#NS"; I i; S name ] -> CB.ns ~at i name
         | [ I at; S "#NI"; I i; I j ] -> CB.ni ~at i j
         | [ I at; S "#US"; I i ] -> CB.us ~at i
         | [ I at; S "#UM"; I i; I j ] -> CB.um ~at i j
         | [ I at; S "#UIM"; I i; I j ] -> CB.uim ~at i j
         | [ I at; S "#UP"; I i ] -> CB.up ~at i
         | [ I at; S "#EV"; I i ] -> CB.ev ~at i
         | [ I at; S "#EA"; I i; I j ] -> CB.ea ~at i j
         | I at :: S "#EC" :: I i :: args ->
           let args =
             List.map
               (function
                 | I i -> i
                 | _ -> failwith "argument must be an int")
               args
           in
           CB.ec ~at i args
         | [ I at; S "#ES"; I i ] -> CB.es ~at i
         | [ I at; S "#EL"; S b; I n; I i; I j ] -> CB.el ~at b n i j
         | [ I at; S "#EP"; S b; I n; I i; I j ] -> CB.ep ~at b n i j
         | _ ->
           incr n_errors;
           Fmt.eprintf "warn: unhandled line %d: %s@." !n_line line
       with e ->
         incr n_errors;
         Fmt.eprintf "error on line %d:@.%s@." !n_line (Printexc.to_string e));

      incr n_line;
      CB.after_line ();

      if !n_errors < max_errors then loop ()
  in

  loop ()
