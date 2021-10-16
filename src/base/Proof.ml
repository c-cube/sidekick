
open Base_types

(* we store steps as binary chunks *)
module CS = Chunk_stack

module Config = struct
  type storage =
    | No_store
    | In_memory
    | On_disk_at of string

  let pp_storage out = function
    | No_store -> Fmt.string out "no-store"
    | In_memory -> Fmt.string out "in-memory"
    | On_disk_at file -> Fmt.fprintf out "(on-file :at %S)" file

  type t = {
    enabled: bool;
    storage: storage;
  }

  let default = { enabled=true; storage=In_memory }
  let empty = { enabled=false; storage=No_store }

  let pp out (self:t) =
    let { enabled; storage } = self in
    Fmt.fprintf out
      "(@[config@ :enabled %B@ :storage %a@])"
      enabled pp_storage storage

  let enable b self = {self with enabled=b}
  let store_in_memory self = {self with storage=In_memory}
  let store_on_disk_at file self = {self with storage=On_disk_at file}
end

(* where we store steps *)
module Storage = struct
  type t =
    | No_store
    | In_memory of CS.Buf.t
    | On_disk of string * out_channel

  let pp out = function
    | No_store -> Fmt.string out "no-store"
    | In_memory _ -> Fmt.string out "in-memory"
    | On_disk (file,_) -> Fmt.fprintf out "(on-file %S)" file
end

(* a step is just a unique integer ID.
   The actual step is stored in the chunk_stack. *)
type proof_step = Proof_ser.ID.t

type lit = Lit.t
type term = Term.t

type t = {
  mutable enabled : bool;
  config: Config.t;
  mutable storage: Storage.t;
  mutable dispose: unit -> unit;
  mutable steps: CS.Writer.t;
}
type proof_rule = t -> proof_step

module Step_vec = struct
  type elt=proof_step
  include VecI32
  let get = get_i32
  let set = set_i32
end

let disable (self:t) : unit =
  self.enabled <- false;
  self.storage <- Storage.No_store;
  self.dispose();
  self.steps <- CS.Writer.dummy;
  ()

let nop_ _ = ()

let create ?(config=Config.default) () : t =
  (* acquire resources for logging *)
  let storage, steps, dispose =
    match config.Config.storage with
    | Config.No_store ->
      Storage.No_store, CS.Writer.dummy, nop_

    | Config.In_memory ->
      let buf = CS.Buf.create ~cap:256 () in
      Storage.In_memory buf, CS.Writer.into_buf buf, nop_

    | Config.On_disk_at file ->
      let oc =
        open_out_gen [Open_creat; Open_wronly; Open_trunc; Open_binary] 0o644 file
      in
      let w = CS.Writer.into_channel oc in
      let dispose () = close_out oc in
      Storage.On_disk (file, oc), w, dispose
  in
  { enabled=config.Config.enabled;
    config;
    steps; storage; dispose; }

let iter_chunks_ (r:CS.Reader.t) k =
  let rec loop () =
    CS.Reader.next r
      ~finish:nop_
      ~yield:(fun b i _len ->
          let step =
            Proof_ser.Bare.of_bytes_exn Proof_ser.Step.decode b ~off:i in
          k step;
          loop ()
        )
  in
  loop ()

let iter_steps_backward (self:t) : Proof_ser.Step.t Iter.t =
  fun yield ->
    begin match self.storage with
      | Storage.No_store -> ()
      | Storage.In_memory buf ->
        let r = CS.Reader.from_buf buf in
        iter_chunks_ r yield
      | Storage.On_disk (file, _oc) ->
        let ic = open_in file in
        let iter = CS.Reader.from_channel_backward ~close_at_end:true ic in
        iter_chunks_ iter yield
    end

let dummy_step : proof_step = -1l

let[@inline] enabled (self:t) = self.enabled

let begin_subproof _ = dummy_step
let end_subproof _ = dummy_step
let del_clause _ _ (_pr:t) = dummy_step
let emit_redundant_clause _ ~hyps:_ _ = dummy_step
let emit_input_clause _ _ = dummy_step
let define_term _ _ _ = dummy_step
let emit_unsat _ _ = dummy_step
let proof_p1 _ _ (_pr:t) = dummy_step
let emit_unsat_core _ (_pr:t) = dummy_step
let lemma_preprocess _ _ ~using:_ (_pr:t) = dummy_step
let lemma_true _ _ = dummy_step
let lemma_cc _ _ = dummy_step
let lemma_rw_clause _ ~using:_ (_pr:t) = dummy_step
let with_defs _ _ (_pr:t) = dummy_step

let lemma_lra _ _ = dummy_step

let lemma_bool_tauto _ _ = dummy_step
let lemma_bool_c _ _ _ = dummy_step
let lemma_bool_equiv _ _ _ = dummy_step
let lemma_ite_true ~ite:_ _ = dummy_step
let lemma_ite_false ~ite:_ _ = dummy_step

let lemma_isa_cstor ~cstor_t:_ _ (_pr:t) = dummy_step
let lemma_select_cstor ~cstor_t:_ _ (_pr:t) = dummy_step
let lemma_isa_split _ _ (_pr:t) = dummy_step
let lemma_isa_sel _ (_pr:t) = dummy_step
let lemma_isa_disj _ _ (_pr:t) = dummy_step
let lemma_cstor_inj _ _ _ (_pr:t) = dummy_step
let lemma_cstor_distinct _ _ (_pr:t) = dummy_step
let lemma_acyclicity _ (_pr:t) = dummy_step
