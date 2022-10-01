open Sidekick_core_logic
module Tr = Sidekick_trace
module ID_cache = LRU.Make (Tr.Entry_id)
module Dec = Ser_decode

type term_ref = Tr.entry_id
type const_decoders = Const.decoders

type t = {
  tst: Term.store;
  src: Tr.Source.t;
  cache: (Term.t, Dec.Error.t) result ID_cache.t;
  mutable const_decode:
    (Const.Ops.t * (Term.t Dec.t -> Const.view Dec.t)) Util.Str_map.t;
      (** tag -> const decoder *)
}

let add_const_decoders (self : t) (decs : Const.decoders) : unit =
  List.iter
    (fun (tag, ops, dec) ->
      (* check that there is no tag collision *)
      if Util.Str_map.mem tag self.const_decode then
        Error.errorf "Trace_reader: two distinct const decoders for tag %S" tag;
      self.const_decode <- Util.Str_map.add tag (ops, dec) self.const_decode)
    decs

let create ?(const_decoders = []) ~source tst : t =
  let self =
    {
      src = source;
      tst;
      cache = ID_cache.create ~size:1024 ();
      const_decode = Util.Str_map.empty;
    }
  in
  List.iter (add_const_decoders self) const_decoders;
  self

let decode_term (self : t) ~read_subterm ~tag : Term.t Dec.t =
  match tag with
  | "TV" ->
    Dec.(
      let+ v, ty = tup2 string read_subterm in
      Term.var_str self.tst v ~ty)
  | "Tv" ->
    Dec.(
      let+ idx, ty = tup2 int read_subterm in
      Term.bvar_i self.tst idx ~ty)
  | "T@" ->
    Dec.(
      let+ f, a = tup2 read_subterm read_subterm in
      Term.app self.tst f a)
  | "Ty" ->
    Dec.(
      let+ i = int in
      Term.type_of_univ self.tst i)
  | "Tl" ->
    Dec.(
      let+ v, ty, bod = tup3 string read_subterm read_subterm in
      Term.DB.lam_db self.tst ~var_name:v ~var_ty:ty bod)
  | "Tp" ->
    Dec.(
      let+ v, ty, bod = tup3 string read_subterm read_subterm in
      Term.DB.pi_db self.tst ~var_name:v ~var_ty:ty bod)
  | "Tc" ->
    Dec.(
      let* view = dict_field_opt "v" any
      and* ty = dict_field "ty" read_subterm
      and* c_tag = dict_field "tag" string in
      let view = Option.value view ~default:Ser_value.null in
      (* look for the decoder for this constant tag *)
      (match Util.Str_map.find_opt c_tag self.const_decode with
      | None -> failf "unknown constant tag %S" c_tag
      | Some (ops, c_dec) ->
        let+ c_view = reflect_or_fail (c_dec read_subterm) view in
        let const = Const.make c_view ops ~ty in
        Term.const self.tst const))
  | "Tf@" ->
    Dec.(
      let+ f = dict_field "f" read_subterm
      and+ l = dict_field "l" (list read_subterm)
      and+ acc0 = dict_field "a0" read_subterm in
      Term.app_fold self.tst ~f l ~acc0)
  | _ -> Dec.failf "unknown tag %S for a term" tag

let rec read_term_err (self : t) (id : term_ref) : _ result =
  (* decoder for subterms *)
  let read_subterm : Term.t Dec.t =
    Dec.(
      let* id = int in
      return_result_err @@ read_term_err self id)
  in

  ID_cache.get self.cache id ~compute:(fun id ->
      match Tr.Source.get_entry self.src id with
      | None ->
        Error
          (Dec.Error.of_string
             (Printf.sprintf "invalid entry: %d" id)
             (Ser_value.int id))
      | Some (tag, v) ->
        let dec = decode_term self ~tag ~read_subterm in
        Dec.run dec v)

let read_term self id =
  Result.map_error Dec.Error.to_string @@ read_term_err self id
