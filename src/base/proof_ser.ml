[@@@ocaml.warning "-26-27"]

(* embedded runtime library *)
module Bare = struct
  
module String_map = Map.Make(String)

let spf = Printf.sprintf

module Decode = struct
  exception Error of string

  type t = {
    bs: bytes;
    mutable off: int;
  }

  type 'a dec = t -> 'a

  let fail_ e = raise (Error e)
  let fail_eof_ what =
    fail_ (spf "unexpected end of input, expected %s" what)

  let uint (self:t) : int64 =
    let rec loop () =
      if self.off >= Bytes.length self.bs then fail_eof_ "uint";
      let c = Char.code (Bytes.get self.bs self.off) in
      self.off <- 1 + self.off; (* consume *)
      if c land 0b1000_0000 <> 0 then (
        let rest = loop() in
        let c = Int64.of_int (c land 0b0111_1111) in
        Int64.(logor (shift_left rest 7) c)
      ) else (
        Int64.of_int c (* done *)
      )
    in
    loop()

  let int (self:t) : int64 =
    let open Int64 in
    let i = uint self in
    let sign_bit = logand 0b1L i in (* true if negative *)
    let sign = equal sign_bit 0L in
    let res =
      if sign then (
        shift_right_logical i 1
      ) else (
        (* put sign back *)
        logor (shift_left 1L 63) (shift_right_logical (lognot i) 1)
      )
    in
    res

  let u8 self : char =
    let x = Bytes.get self.bs self.off in
    self.off <- self.off + 1;
    x
  let i8 = u8

  let u16 self =
    let x = Bytes.get_int16_le self.bs self.off in
    self.off <- self.off + 2;
    x
  let i16 = u16

  let u32 self =
    let x = Bytes.get_int32_le self.bs self.off in
    self.off <- self.off + 4;
    x
  let i32 = u32

  let u64 self =
    let i = Bytes.get_int64_le self.bs self.off in
    self.off <- 8 + self.off;
    i
  let i64 = u64

  let bool self : bool =
    let c = Bytes.get self.bs self.off in
    self.off <- 1 + self.off;
    Char.code c <> 0

  let f32 (self:t) : float =
    let i = i32 self in
    Int32.float_of_bits i

  let f64 (self:t) : float =
    let i = i64 self in
    Int64.float_of_bits i

  let data_of ~size self : bytes =
    let s = Bytes.sub self.bs self.off size in
    self.off <- self.off + size;
    s

  let data self : bytes =
    let size = uint self in
    if Int64.compare size (Int64.of_int Sys.max_string_length) > 0 then
      fail_ "string too large";
    let size = Int64.to_int size in (* fits, because of previous test *)
    data_of ~size self

  let string self : string =
    Bytes.unsafe_to_string (data self)

  let[@inline] optional dec self : _ option =
    let c = u8 self in
    if Char.code c = 0 then None else Some (dec self)
end

module Encode = struct
  type t = Buffer.t

  let of_buffer buf : t = buf

  type 'a enc = t -> 'a -> unit

  (* no need to check for overflow below *)
  external unsafe_chr : int -> char = "%identity"

  let uint (self:t) (i:int64) : unit =
    let module I = Int64 in
    let i = ref i in
    let continue = ref true in
    while !continue do
      let j = I.logand 0b0111_1111L !i in
      if !i = j then (
        continue := false;
        let j = I.to_int j in
        Buffer.add_char self (unsafe_chr j)
      ) else (
        (* set bit 8 to [1] *)
        let lsb = I.to_int (I.logor 0b1000_0000L j) in
        let lsb = (unsafe_chr lsb) in
        Buffer.add_char self lsb;
        i := I.shift_right_logical !i 7;
      )
    done

  let[@inline] int (self:t) i =
    let open Int64 in
    let ui = logxor (shift_left i 1) (shift_right i 63) in
    uint self ui

  let u8 self x = Buffer.add_char self x
  let i8 = u8
  let u16 self x = Buffer.add_int16_le self x
  let i16 = u16
  let u32 self x = Buffer.add_int32_le self x
  let i32 = u32
  let u64 self x = Buffer.add_int64_le self x
  let i64 = u64

  let bool self x = Buffer.add_char self (if x then Char.chr 1 else Char.chr 0)

  let f64 (self:t) x = Buffer.add_int64_le self (Int64.bits_of_float x)

  let data_of ~size self x =
    if size <> Bytes.length x then failwith "invalid length for Encode.data_of";
    Buffer.add_bytes self x

  let data self x =
    uint self (Int64.of_int (Bytes.length x));
    Buffer.add_bytes self x

  let string self x = data self (Bytes.unsafe_of_string x)

  let[@inline] optional enc self x : unit =
    match x with
    | None -> u8 self (Char.chr 0)
    | Some x ->
      u8 self (Char.chr 1);
      enc self x
end

let to_string (e:'a Encode.enc) (x:'a) =
  let buf = Buffer.create 32 in
  e buf x;
  Buffer.contents buf

let of_bytes_exn ?(off=0) dec bs =
  let i = {Decode.bs; off} in
  dec i

let of_bytes ?off dec bs =
  try Ok (of_bytes_exn ?off dec bs)
  with Decode.Error e -> Error e

let of_string_exn dec s = of_bytes_exn dec (Bytes.unsafe_of_string s)
let of_string dec s = of_bytes dec (Bytes.unsafe_of_string s)


(*$inject
  let to_s f x =
    let buf = Buffer.create 32 in
    let out = Encode.of_buffer buf in
    f out x;
    Buffer.contents buf

  let of_s f x =
    let i = {Decode.off=0; bs=Bytes.unsafe_of_string x} in
    f i
*)

(*$= & ~printer:Int64.to_string
  37L (of_s Decode.uint (to_s Encode.uint 37L))
  42L (of_s Decode.uint (to_s Encode.uint 42L))
  0L (of_s Decode.uint (to_s Encode.uint 0L))
  105542252L (of_s Decode.uint (to_s Encode.uint 105542252L))
  Int64.max_int (of_s Decode.uint (to_s Encode.uint Int64.max_int))
*)

(*$= & ~printer:Int64.to_string
  37L (of_s Decode.int (to_s Encode.int 37L))
  42L (of_s Decode.int (to_s Encode.int 42L))
  0L (of_s Decode.int (to_s Encode.int 0L))
  105542252L (of_s Decode.int (to_s Encode.int 105542252L))
  Int64.max_int (of_s Decode.int (to_s Encode.int Int64.max_int))
  Int64.min_int (of_s Decode.int (to_s Encode.int Int64.min_int))
  (-1209433446454112432L) (of_s Decode.int (to_s Encode.int (-1209433446454112432L)))
  (-3112855215860398414L) (of_s Decode.int (to_s Encode.int (-3112855215860398414L)))
*)

(*$=
  1 (let s = to_s Encode.int (-1209433446454112432L) in 0x1 land (Char.code s.[0]))
*)

(*$Q
  Q.(int64) (fun s -> \
    s = (of_s Decode.uint (to_s Encode.uint s)))
*)

(*$Q
  Q.(int64) (fun s -> \
    s = (of_s Decode.int (to_s Encode.int s)))
*)

(* TODO: some tests with qtest *)

end

module ID = struct
  type t = int32
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    Bare.Decode.i32 dec
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    Bare.Encode.i32 enc self
  
end

module Lit = struct
  type t = int64
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    Bare.Decode.int dec
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    Bare.Encode.int enc self
  
end

module Clause = struct
  type t = {
    lits: Lit.t array;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let lits =
      (let len = Bare.Decode.uint dec in
       if len>Int64.of_int Sys.max_array_length then raise (Bare.Decode.Error"array too big");
       Array.init (Int64.to_int len) (fun _ -> Lit.decode dec)) in
    {lits; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      (let arr = self.lits in
       Bare.Encode.uint enc (Int64.of_int (Array.length arr));
       Array.iter (fun xi -> Lit.encode enc xi) arr);
    end
  
end

module Step_rup = struct
  type t = {
    res: Clause.t;
    steps: ID.t array;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let res = Clause.decode dec in
    let steps =
      (let len = Bare.Decode.uint dec in
       if len>Int64.of_int Sys.max_array_length then raise (Bare.Decode.Error"array too big");
       Array.init (Int64.to_int len) (fun _ -> ID.decode dec)) in
    {res; steps; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      Clause.encode enc self.res;
      (let arr = self.steps in
       Bare.Encode.uint enc (Int64.of_int (Array.length arr));
       Array.iter (fun xi -> ID.encode enc xi) arr);
    end
  
end

module Step_bridge_lit_expr = struct
  type t = {
    lit: Lit.t;
    expr: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let lit = Lit.decode dec in let expr = ID.decode dec in {lit; expr; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin Lit.encode enc self.lit; ID.encode enc self.expr; end
  
end

module Step_cc = struct
  type t = {
    eqns: ID.t array;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let eqns =
      (let len = Bare.Decode.uint dec in
       if len>Int64.of_int Sys.max_array_length then raise (Bare.Decode.Error"array too big");
       Array.init (Int64.to_int len) (fun _ -> ID.decode dec)) in
    {eqns; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      (let arr = self.eqns in
       Bare.Encode.uint enc (Int64.of_int (Array.length arr));
       Array.iter (fun xi -> ID.encode enc xi) arr);
    end
  
end

module Step_preprocess = struct
  type t = {
    t: ID.t;
    u: ID.t;
    using: ID.t array;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let t = ID.decode dec in
    let u = ID.decode dec in
    let using =
      (let len = Bare.Decode.uint dec in
       if len>Int64.of_int Sys.max_array_length then raise (Bare.Decode.Error"array too big");
       Array.init (Int64.to_int len) (fun _ -> ID.decode dec)) in
    {t; u; using; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      ID.encode enc self.t;
      ID.encode enc self.u;
      (let arr = self.using in
       Bare.Encode.uint enc (Int64.of_int (Array.length arr));
       Array.iter (fun xi -> ID.encode enc xi) arr);
    end
  
end

module Step_view = struct
  type t =
    | Step_rup of Step_rup.t
    | Step_bridge_lit_expr of Step_bridge_lit_expr.t
    | Step_cc of Step_cc.t
    | Step_preprocess of Step_preprocess.t
    
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let tag = Bare.Decode.uint dec in
    match tag with
    | 0L -> Step_rup (Step_rup.decode dec)
    | 1L -> Step_bridge_lit_expr (Step_bridge_lit_expr.decode dec)
    | 2L -> Step_cc (Step_cc.decode dec)
    | 3L -> Step_preprocess (Step_preprocess.decode dec)
    | _ -> raise (Bare.Decode.Error(Printf.sprintf "unknown union tag Step_view.t: %Ld" tag))
    
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    match self with
    | Step_rup x ->
      Bare.Encode.uint enc 0L;
      Step_rup.encode enc x
    | Step_bridge_lit_expr x ->
      Bare.Encode.uint enc 1L;
      Step_bridge_lit_expr.encode enc x
    | Step_cc x ->
      Bare.Encode.uint enc 2L;
      Step_cc.encode enc x
    | Step_preprocess x ->
      Bare.Encode.uint enc 3L;
      Step_preprocess.encode enc x
    
    
end

module Step = struct
  type t = {
    id: ID.t;
    view: Step_view.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let id = ID.decode dec in let view = Step_view.decode dec in {id; view; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.id; Step_view.encode enc self.view; end
  
end


