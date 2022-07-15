module CS = Chunk_stack

type t = No_store | In_memory of CS.Buf.t | On_disk of string * out_channel

let pp out = function
  | No_store -> Fmt.string out "no-store"
  | In_memory _ -> Fmt.string out "in-memory"
  | On_disk (file, _) -> Fmt.fprintf out "(on-file %S)" file

let nop_ _ = ()

let iter_chunks_ (r : CS.Reader.t) k =
  let rec loop () =
    CS.Reader.next r ~finish:nop_ ~yield:(fun b i _len ->
        let step = Proof_ser.Bare.of_bytes_exn Proof_ser.Step.decode b ~off:i in
        k step;
        loop ())
  in
  loop ()

let iter_steps_backward (self : t) : Proof_ser.Step.t Iter.t =
  let module CS = Chunk_stack in
  fun yield ->
    match self with
    | No_store -> ()
    | In_memory buf ->
      let r = CS.Reader.from_buf buf in
      iter_chunks_ r yield
    | On_disk (file, _oc) ->
      let ic = open_in file in
      let iter = CS.Reader.from_channel_backward ~close_at_end:true ic in
      iter_chunks_ iter yield
