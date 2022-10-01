open Sidekick_core
module Tr = Sidekick_trace

type entry = Assert of Term.t | Assert_clause of Lit.t list

let pp_entry out = function
  | Assert t -> Fmt.fprintf out "(@[assert@ %a@])" Term.pp t
  | Assert_clause c ->
    Fmt.fprintf out "(@[assert-c@ %a@])" (Fmt.Dump.list Lit.pp) c

type t = { tst: Term.store; src: Tr.Source.t; t_dec: Term.Trace_reader.t }

let create ?const_decoders tst src : t =
  let t_dec = Term.Trace_reader.create ?const_decoders tst ~source:src in
  { tst; src; t_dec }

let add_const_decoders self c = Term.Trace_reader.add_const_decoders self.t_dec c

let dec_t (self : t) =
  Ser_decode.(
    let* i = int in
    return_result @@ Term.Trace_reader.read_term self.t_dec i)

let dec_c (self : t) =
  Ser_decode.(
    let dec_lit =
      let+ b, t = tup2 bool @@ dec_t self in
      Lit.atom self.tst ~sign:b t
    in
    list dec_lit)

let decode (self : t) ~tag v =
  Log.debugf 30 (fun k ->
      k "(@[trace-reader.decode@ :tag %S@ :val %a@])" tag Ser_value.pp v);
  match tag with
  | "Asst" ->
    (match Ser_decode.(run (dec_t self) v) with
    | Ok t -> Some (Assert t)
    | Error err ->
      Fmt.eprintf "cannot decode entry with tag %S:@ %a@." tag
        Ser_decode.Error.pp err;
      None)
  | "AssC" ->
    Ser_decode.(
      (match run (dec_c self) v with
      | Ok c -> Some (Assert_clause c)
      | Error err ->
        Fmt.eprintf "cannot decode entry with tag %S:@ %a@." tag
          Ser_decode.Error.pp err;
        None))
  | _ -> None

let decode_entry self id : _ option =
  let tag, v = Tr.Source.get_entry_exn self.src id in
  decode self ~tag v
