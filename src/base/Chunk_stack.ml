
module Buf = struct
  type t = {
    mutable b: bytes;
    mutable len: int;
  }

  let create ?(cap=16) () : t =
    { len=0; b=Bytes.create cap; }

  let ensure_size_ (self:t) (new_len:int) : unit =
    if new_len > Bytes.length self.b then (
      let size = min (new_len + new_len / 4 + 5) Sys.max_string_length in
      if new_len > size then failwith "max buf size exceeded";

      let b2 = Bytes.create size in
      Bytes.blit self.b 0 b2 0 self.len;
      self.b <- b2
    )

  let add_bytes (self:t) (b:bytes) (off:int) (len:int) =
    ensure_size_ self (self.len + len);
    Bytes.blit self.b self.len b off len;
    self.len <- self.len + len

  let[@inline] add_buf (self:t) (other:t) =
    add_bytes self other.b 0 other.len

  let clear self = self.len <- 0

  let contents self = Bytes.sub_string self.b 0 self.len
end

module Writer = struct
  type t = {
    write: Buf.t -> unit;
  }

  let nop_ _ = ()

  let dummy : t = { write=nop_; }

  let into_buf (into:Buf.t) : t =
    let blen = Bytes.create 4 in
    let write buf =
      Buf.add_buf into buf;
      (* add len *)
      Bytes.set_int32_le blen 0 (Int32.of_int buf.Buf.len);
      Buf.add_bytes into blen 0 4;
    in
    { write; }

  let into_channel (oc:out_channel) : t =
    let blen = Bytes.create 4 in
    let write buf =
      output oc buf.Buf.b 0 buf.Buf.len;
      (* add len *)
      Bytes.set_int32_le blen 0 (Int32.of_int buf.Buf.len);
      output oc blen 0 4
    in
    { write; }
end

module Reader = struct
  type t = {
    read: Buf.t -> bool;
  }

  let[@inline] next (self:t) buf : bool = self.read buf

  let empty : t = { read=fun _ -> false }

  let from_buf (buf:Buf.t) : t =
    assert false (* TODO *)

  let with_file_backward (filename:string) f =
    CCIO.with_in ~flags:[Open_binary; Open_rdonly] filename @@ fun ic ->

    let len = in_channel_length ic in
    seek_in ic len;

    (* read length *)
    let blen = Bytes.create 4 in

    let read buf : bool =
      let pos = pos_in ic in
      if pos > 0 then (
        (* read length of preceding chunk *)
        assert (pos>=4);
        seek_in ic (pos - 4);

        really_input ic blen 0 4;
        let chunk_len = Int32.to_int (Bytes.get_int32_le blen 0) in
        Printf.printf "read chunk of len %d\n%!" chunk_len;

        (* now read chunk *)
        Buf.ensure_size_ buf chunk_len;
        seek_in ic (pos - 4 - chunk_len);
        really_input ic buf.Buf.b 0 chunk_len;
        buf.Buf.len <- chunk_len;

        true
      ) else (
        false
      )
    in
    f {read}
end

(*$T
    false
    *)
