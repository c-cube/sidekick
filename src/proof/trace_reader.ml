open Sidekick_core
module Tr = Sidekick_trace
module Dec = Ser_decode
open Dec.Infix

type step_id = Step.id
type t = { src: Tr.Source.t; t_reader: Term.Trace_reader.t }

let create ~src t_reader : t = { src; t_reader }

let rec read_step ?(fix = false) (self : t) (id : step_id) : _ result =
  match Tr.Source.get_entry self.src id with
  | Some ("Pt", v) ->
    let res = Dec.run (Pterm.deser self.t_reader) v in
    (match res with
    | Ok (Pterm.P_ref id') when fix ->
      (* read reference recursively *)
      read_step ~fix self id'
    | _ -> res)
  | None ->
    Error (Dec.Error.of_string "unknown source entry" (Ser_value.int id))
  | Some (tag, _) ->
    Error
      (Dec.Error.of_string "expected proof term, wrong tag"
         (Ser_value.string tag))

let dec_step_id ?fix (self : t) =
  let* id = Dec.int in
  read_step ?fix self id |> Dec.return_result_err
