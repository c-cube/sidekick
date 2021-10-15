
module Buf = struct
  type t = {
    mutable b: bytes;
    mutable len: int;
  }

  let create ?(cap=16) () : t =
    { len=0; b=Bytes.create cap; }

  let resize_ self new_len : unit =
    let size = min (new_len + new_len / 4 + 5) Sys.max_string_length in
    if new_len > size then failwith "max buf size exceeded";

    let b2 = Bytes.create size in
    Bytes.blit self.b 0 b2 0 self.len;
    self.b <- b2

  let[@inline] ensure_size_ (self:t) (new_len:int) : unit =
    if new_len > Bytes.length self.b then (
      resize_ self new_len
    )

  let add_bytes (self:t) (b:bytes) (off:int) (len:int) =
    Printf.printf "add_bytes len=%d\n%!" len;
    ensure_size_ self (self.len + len);
    Bytes.blit b off self.b self.len len;
    self.len <- self.len + len

  let[@inline] add_buf (self:t) (other:t) =
    add_bytes self other.b 0 other.len

  let clear self = self.len <- 0

  let contents self = Bytes.sub_string self.b 0 self.len
end

module Writer = struct
  type t = {
    write: bytes -> int -> int -> unit;
  }

  let nop_ _ = ()

  let dummy : t = { write=fun _ _ _ -> (); }

  let into_buf (into:Buf.t) : t =
    let blen = Bytes.create 4 in
    let write b i len =
      Buf.add_bytes into b i len;
      (* add len *)
      Bytes.set_int32_le blen 0 (Int32.of_int len);
      Buf.add_bytes into blen 0 4;
    in
    { write; }

  let into_channel (oc:out_channel) : t =
    let blen = Bytes.create 4 in
    let write b i len =
      output oc b i len;
      (* add len *)
      Bytes.set_int32_le blen 0 (Int32.of_int len);
      output oc blen 0 4
    in
    { write; }

  let[@inline] add_buf self buf = self.write buf.Buf.b 0 buf.Buf.len
  let[@inline] add_bytes self b i len = self.write b i len
  let[@inline] add_string self s =
    add_bytes self (Bytes.unsafe_of_string s) 0 (String.length s)
end

module Reader = struct
  type t = {
    read: 'a. yield:(bytes -> int -> int -> 'a) -> finish:(unit -> 'a) -> 'a;
  } [@@unboxed]

  let[@inline] next (self:t) f : bool =
    self.read
      ~yield:(fun b i len -> f b i len; true)
      ~finish:(fun () -> false)

  let next_string (self:t) : string option =
    self.read
      ~yield:(fun b i len -> Some (Bytes.sub_string b i len))
      ~finish:(fun () -> None)

  let empty : t = { read=fun ~yield:_ ~finish -> finish() }

  let from_buf (ibuf:Buf.t) : t =
    let i = ref ibuf.Buf.len in

    (* read next record *)
    let read ~yield ~finish =
      if !i > 0 then (
        Printf.printf "reading (!i = %d)\n%!" !i;
        assert (!i >= 4);

        i := !i - 4;
        let chunk_size = Int32.to_int (Bytes.get_int32_le ibuf.Buf.b !i) in
        Printf.printf "chunk size is %d\n%!" chunk_size;

        i := !i - chunk_size;
        yield ibuf.Buf.b !i chunk_size
      ) else (
        finish()
      )
    in
    { read; }

  let with_file_backward (filename:string) f =
    CCIO.with_in ~flags:[Open_binary; Open_rdonly] filename @@ fun ic ->

    let len = in_channel_length ic in
    seek_in ic len;

    let blen = Bytes.create 4 in (* to read length *)
    let buf = Buf.create() in (* local buffer *)

    let read ~yield ~finish =
      let pos = pos_in ic in
      if pos > 0 then (
        (* read length of preceding chunk *)
        assert (pos>=4);
        seek_in ic (pos - 4);

        really_input ic blen 0 4;
        let chunk_len = Int32.to_int (Bytes.get_int32_le blen 0) in

        (* now read chunk *)
        Buf.ensure_size_ buf chunk_len;
        seek_in ic (pos - 4 - chunk_len);
        really_input ic buf.Buf.b 0 chunk_len;
        buf.Buf.len <- chunk_len;

        yield buf.Buf.b 0 buf.Buf.len
      ) else (
        finish()
      )
    in
    f {read}
end

(*$T
    false
    *)
