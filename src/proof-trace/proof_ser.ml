(* generated from "proof_ser.bare" using bare-codegen *)
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

module Pp = struct
  type 'a t = Format.formatter -> 'a -> unit
  type 'a iter = ('a -> unit) -> unit
  let unit out () = Format.pp_print_string out "()"
  let int8 out c = Format.fprintf out "%d" (Char.code c)
  let int out x = Format.fprintf out "%d" x
  let int32 out x = Format.fprintf out "%ld" x
  let int64 out x = Format.fprintf out "%Ld" x
  let float out x = Format.fprintf out "%h" x
  let bool = Format.pp_print_bool
  let string out x = Format.fprintf out "%S" x
  let data out x = string out (Bytes.unsafe_to_string x)
  let option ppelt out x = match x with
    | None -> Format.fprintf out "None"
    | Some x -> Format.fprintf out "(Some %a)" ppelt x
  let array ppelt out x =
    Format.fprintf out "[@[";
    Array.iteri (fun i x ->
        if i>0 then Format.fprintf out ";@ ";
        ppelt out x)
      x;
    Format.fprintf out "@]]"
  let iter ppelt out xs =
    Format.fprintf out "[@[";
    let i = ref 0 in
    xs (fun x ->
        if !i>0 then Format.fprintf out ",@ ";
        incr i;
        ppelt out x);
    Format.fprintf out "@]]"
  let list ppelt out l = iter ppelt out (fun f->List.iter f l)
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

(*$Q & ~count:1000
  Q.(int64) (fun s -> \
    s = (of_s Decode.uint (to_s Encode.uint s)))
  Q.(small_nat) (fun n -> \
    let n = Int64.of_int n in \
    n = (of_s Decode.uint (to_s Encode.uint n)))
*)

(*$Q & ~count:1000
  Q.(int64) (fun s -> \
    s = (of_s Decode.int (to_s Encode.int s)))
  Q.(small_signed_int) (fun n -> \
    let n = Int64.of_int n in \
    n = (of_s Decode.int (to_s Encode.int n)))
*)

(*$R
    for i=0 to 1_000 do
      let i = Int64.of_int i in
      assert_equal ~printer:Int64.to_string i (of_s Decode.int (to_s Encode.int i))
    done
*)

(*$R
    for i=0 to 1_000 do
      let i = Int64.of_int i in
      assert_equal ~printer:Int64.to_string i (of_s Decode.uint (to_s Encode.uint i))
    done
*)

(*$Q & ~count:1000
  Q.(string) (fun s -> \
    s = (of_s Decode.string (to_s Encode.string s)))
*)

end

module ID = struct
  type t = int32
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    Bare.Decode.i32 dec
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    Bare.Encode.i32 enc self
  
  let pp out (self:t) : unit =
    Bare.Pp.int32 out self
  
end

module Lit = struct
  type t = ID.t
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    ID.decode dec
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    ID.encode enc self
  
  let pp out (self:t) : unit =
    ID.pp out self
  
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
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "lits=%a;@ " (Bare.Pp.array Lit.pp) x.lits;
       Format.fprintf out "@]}";
     end) out self

end

module Step_input = struct
  type t = {
    c: Clause.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let c = Clause.decode dec in {c; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin Clause.encode enc self.c; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "c=%a;@ " Clause.pp x.c;
       Format.fprintf out "@]}";
     end) out self

end

module Step_rup = struct
  type t = {
    res: Clause.t;
    hyps: ID.t array;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let res = Clause.decode dec in
    let hyps =
      (let len = Bare.Decode.uint dec in
       if len>Int64.of_int Sys.max_array_length then raise (Bare.Decode.Error"array too big");
       Array.init (Int64.to_int len) (fun _ -> ID.decode dec)) in
    {res; hyps; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      Clause.encode enc self.res;
      (let arr = self.hyps in
       Bare.Encode.uint enc (Int64.of_int (Array.length arr));
       Array.iter (fun xi -> ID.encode enc xi) arr);
    end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "res=%a;@ " Clause.pp x.res;
       Format.fprintf out "hyps=%a;@ " (Bare.Pp.array ID.pp) x.hyps;
       Format.fprintf out "@]}";
     end) out self

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
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "lit=%a;@ " Lit.pp x.lit;
       Format.fprintf out "expr=%a;@ " ID.pp x.expr;
       Format.fprintf out "@]}";
     end) out self

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
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "eqns=%a;@ " (Bare.Pp.array ID.pp) x.eqns;
       Format.fprintf out "@]}";
     end) out self

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
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "t=%a;@ " ID.pp x.t;
       Format.fprintf out "u=%a;@ " ID.pp x.u;
       Format.fprintf out "using=%a;@ " (Bare.Pp.array ID.pp) x.using;
       Format.fprintf out "@]}";
     end) out self

end

module Step_clause_rw = struct
  type t = {
    c: ID.t;
    res: Clause.t;
    using: ID.t array;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let c = ID.decode dec in
    let res = Clause.decode dec in
    let using =
      (let len = Bare.Decode.uint dec in
       if len>Int64.of_int Sys.max_array_length then raise (Bare.Decode.Error"array too big");
       Array.init (Int64.to_int len) (fun _ -> ID.decode dec)) in
    {c; res; using; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      ID.encode enc self.c;
      Clause.encode enc self.res;
      (let arr = self.using in
       Bare.Encode.uint enc (Int64.of_int (Array.length arr));
       Array.iter (fun xi -> ID.encode enc xi) arr);
    end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "c=%a;@ " ID.pp x.c;
       Format.fprintf out "res=%a;@ " Clause.pp x.res;
       Format.fprintf out "using=%a;@ " (Bare.Pp.array ID.pp) x.using;
       Format.fprintf out "@]}";
     end) out self

end

module Step_unsat = struct
  type t = {
    c: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let c = ID.decode dec in {c; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.c; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "c=%a;@ " ID.pp x.c;
       Format.fprintf out "@]}";
     end) out self

end

module Step_proof_p1 = struct
  type t = {
    rw_with: ID.t;
    c: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let rw_with = ID.decode dec in let c = ID.decode dec in {rw_with; c; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.rw_with; ID.encode enc self.c; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "rw_with=%a;@ " ID.pp x.rw_with;
       Format.fprintf out "c=%a;@ " ID.pp x.c;
       Format.fprintf out "@]}";
     end) out self

end

module Step_proof_r1 = struct
  type t = {
    unit: ID.t;
    c: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let unit = ID.decode dec in let c = ID.decode dec in {unit; c; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.unit; ID.encode enc self.c; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "unit=%a;@ " ID.pp x.unit;
       Format.fprintf out "c=%a;@ " ID.pp x.c;
       Format.fprintf out "@]}";
     end) out self

end

module Step_proof_res = struct
  type t = {
    pivot: ID.t;
    c1: ID.t;
    c2: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let pivot = ID.decode dec in
    let c1 = ID.decode dec in
    let c2 = ID.decode dec in
    {pivot; c1; c2; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      ID.encode enc self.pivot;
      ID.encode enc self.c1;
      ID.encode enc self.c2;
    end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "pivot=%a;@ " ID.pp x.pivot;
       Format.fprintf out "c1=%a;@ " ID.pp x.c1;
       Format.fprintf out "c2=%a;@ " ID.pp x.c2;
       Format.fprintf out "@]}";
     end) out self

end

module Step_bool_tauto = struct
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
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "lits=%a;@ " (Bare.Pp.array Lit.pp) x.lits;
       Format.fprintf out "@]}";
     end) out self

end

module Step_bool_c = struct
  type t = {
    rule: string;
    exprs: ID.t array;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let rule = Bare.Decode.string dec in
    let exprs =
      (let len = Bare.Decode.uint dec in
       if len>Int64.of_int Sys.max_array_length then raise (Bare.Decode.Error"array too big");
       Array.init (Int64.to_int len) (fun _ -> ID.decode dec)) in
    {rule; exprs; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      Bare.Encode.string enc self.rule;
      (let arr = self.exprs in
       Bare.Encode.uint enc (Int64.of_int (Array.length arr));
       Array.iter (fun xi -> ID.encode enc xi) arr);
    end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "rule=%a;@ " Bare.Pp.string x.rule;
       Format.fprintf out "exprs=%a;@ " (Bare.Pp.array ID.pp) x.exprs;
       Format.fprintf out "@]}";
     end) out self

end

module Step_true = struct
  type t = {
    true_: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let true_ = ID.decode dec in {true_; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.true_; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "true_=%a;@ " ID.pp x.true_;
       Format.fprintf out "@]}";
     end) out self

end

module Fun_decl = struct
  type t = {
    f: string;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let f = Bare.Decode.string dec in {f; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin Bare.Encode.string enc self.f; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "f=%a;@ " Bare.Pp.string x.f;
       Format.fprintf out "@]}";
     end) out self

end

module Expr_def = struct
  type t = {
    c: ID.t;
    rhs: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let c = ID.decode dec in let rhs = ID.decode dec in {c; rhs; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.c; ID.encode enc self.rhs; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "c=%a;@ " ID.pp x.c;
       Format.fprintf out "rhs=%a;@ " ID.pp x.rhs;
       Format.fprintf out "@]}";
     end) out self

end

module Expr_bool = struct
  type t = {
    b: bool;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let b = Bare.Decode.bool dec in {b; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin Bare.Encode.bool enc self.b; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "b=%a;@ " Bare.Pp.bool x.b;
       Format.fprintf out "@]}";
     end) out self

end

module Expr_if = struct
  type t = {
    cond: ID.t;
    then_: ID.t;
    else_: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let cond = ID.decode dec in
    let then_ = ID.decode dec in
    let else_ = ID.decode dec in
    {cond; then_; else_; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      ID.encode enc self.cond;
      ID.encode enc self.then_;
      ID.encode enc self.else_;
    end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "cond=%a;@ " ID.pp x.cond;
       Format.fprintf out "then_=%a;@ " ID.pp x.then_;
       Format.fprintf out "else_=%a;@ " ID.pp x.else_;
       Format.fprintf out "@]}";
     end) out self

end

module Expr_not = struct
  type t = {
    f: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let f = ID.decode dec in {f; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.f; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "f=%a;@ " ID.pp x.f;
       Format.fprintf out "@]}";
     end) out self

end

module Expr_eq = struct
  type t = {
    lhs: ID.t;
    rhs: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let lhs = ID.decode dec in let rhs = ID.decode dec in {lhs; rhs; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.lhs; ID.encode enc self.rhs; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "lhs=%a;@ " ID.pp x.lhs;
       Format.fprintf out "rhs=%a;@ " ID.pp x.rhs;
       Format.fprintf out "@]}";
     end) out self

end

module Expr_app = struct
  type t = {
    f: ID.t;
    args: ID.t array;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let f = ID.decode dec in
    let args =
      (let len = Bare.Decode.uint dec in
       if len>Int64.of_int Sys.max_array_length then raise (Bare.Decode.Error"array too big");
       Array.init (Int64.to_int len) (fun _ -> ID.decode dec)) in
    {f; args; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin
      ID.encode enc self.f;
      (let arr = self.args in
       Bare.Encode.uint enc (Int64.of_int (Array.length arr));
       Array.iter (fun xi -> ID.encode enc xi) arr);
    end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "f=%a;@ " ID.pp x.f;
       Format.fprintf out "args=%a;@ " (Bare.Pp.array ID.pp) x.args;
       Format.fprintf out "@]}";
     end) out self

end

module Expr_isa = struct
  type t = {
    c: ID.t;
    arg: ID.t;
  }
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let c = ID.decode dec in let arg = ID.decode dec in {c; arg; }
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    begin ID.encode enc self.c; ID.encode enc self.arg; end
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "c=%a;@ " ID.pp x.c;
       Format.fprintf out "arg=%a;@ " ID.pp x.arg;
       Format.fprintf out "@]}";
     end) out self

end

module Step_view = struct
  type t =
    | Step_input of Step_input.t
    | Step_unsat of Step_unsat.t
    | Step_rup of Step_rup.t
    | Step_bridge_lit_expr of Step_bridge_lit_expr.t
    | Step_cc of Step_cc.t
    | Step_preprocess of Step_preprocess.t
    | Step_clause_rw of Step_clause_rw.t
    | Step_bool_tauto of Step_bool_tauto.t
    | Step_bool_c of Step_bool_c.t
    | Step_proof_p1 of Step_proof_p1.t
    | Step_proof_r1 of Step_proof_r1.t
    | Step_proof_res of Step_proof_res.t
    | Step_true of Step_true.t
    | Fun_decl of Fun_decl.t
    | Expr_def of Expr_def.t
    | Expr_bool of Expr_bool.t
    | Expr_if of Expr_if.t
    | Expr_not of Expr_not.t
    | Expr_isa of Expr_isa.t
    | Expr_eq of Expr_eq.t
    | Expr_app of Expr_app.t
    
  
  (** @raise Bare.Decode.Error in case of error. *)
  let decode (dec: Bare.Decode.t) : t =
    let tag = Bare.Decode.uint dec in
    match tag with
    | 0L -> Step_input (Step_input.decode dec)
    | 1L -> Step_unsat (Step_unsat.decode dec)
    | 2L -> Step_rup (Step_rup.decode dec)
    | 3L -> Step_bridge_lit_expr (Step_bridge_lit_expr.decode dec)
    | 4L -> Step_cc (Step_cc.decode dec)
    | 5L -> Step_preprocess (Step_preprocess.decode dec)
    | 6L -> Step_clause_rw (Step_clause_rw.decode dec)
    | 7L -> Step_bool_tauto (Step_bool_tauto.decode dec)
    | 8L -> Step_bool_c (Step_bool_c.decode dec)
    | 9L -> Step_proof_p1 (Step_proof_p1.decode dec)
    | 10L -> Step_proof_r1 (Step_proof_r1.decode dec)
    | 11L -> Step_proof_res (Step_proof_res.decode dec)
    | 12L -> Step_true (Step_true.decode dec)
    | 13L -> Fun_decl (Fun_decl.decode dec)
    | 14L -> Expr_def (Expr_def.decode dec)
    | 15L -> Expr_bool (Expr_bool.decode dec)
    | 16L -> Expr_if (Expr_if.decode dec)
    | 17L -> Expr_not (Expr_not.decode dec)
    | 18L -> Expr_isa (Expr_isa.decode dec)
    | 19L -> Expr_eq (Expr_eq.decode dec)
    | 20L -> Expr_app (Expr_app.decode dec)
    | _ -> raise (Bare.Decode.Error(Printf.sprintf "unknown union tag Step_view.t: %Ld" tag))
    
  
  let encode (enc: Bare.Encode.t) (self: t) : unit =
    match self with
    | Step_input x ->
      Bare.Encode.uint enc 0L;
      Step_input.encode enc x
    | Step_unsat x ->
      Bare.Encode.uint enc 1L;
      Step_unsat.encode enc x
    | Step_rup x ->
      Bare.Encode.uint enc 2L;
      Step_rup.encode enc x
    | Step_bridge_lit_expr x ->
      Bare.Encode.uint enc 3L;
      Step_bridge_lit_expr.encode enc x
    | Step_cc x ->
      Bare.Encode.uint enc 4L;
      Step_cc.encode enc x
    | Step_preprocess x ->
      Bare.Encode.uint enc 5L;
      Step_preprocess.encode enc x
    | Step_clause_rw x ->
      Bare.Encode.uint enc 6L;
      Step_clause_rw.encode enc x
    | Step_bool_tauto x ->
      Bare.Encode.uint enc 7L;
      Step_bool_tauto.encode enc x
    | Step_bool_c x ->
      Bare.Encode.uint enc 8L;
      Step_bool_c.encode enc x
    | Step_proof_p1 x ->
      Bare.Encode.uint enc 9L;
      Step_proof_p1.encode enc x
    | Step_proof_r1 x ->
      Bare.Encode.uint enc 10L;
      Step_proof_r1.encode enc x
    | Step_proof_res x ->
      Bare.Encode.uint enc 11L;
      Step_proof_res.encode enc x
    | Step_true x ->
      Bare.Encode.uint enc 12L;
      Step_true.encode enc x
    | Fun_decl x ->
      Bare.Encode.uint enc 13L;
      Fun_decl.encode enc x
    | Expr_def x ->
      Bare.Encode.uint enc 14L;
      Expr_def.encode enc x
    | Expr_bool x ->
      Bare.Encode.uint enc 15L;
      Expr_bool.encode enc x
    | Expr_if x ->
      Bare.Encode.uint enc 16L;
      Expr_if.encode enc x
    | Expr_not x ->
      Bare.Encode.uint enc 17L;
      Expr_not.encode enc x
    | Expr_isa x ->
      Bare.Encode.uint enc 18L;
      Expr_isa.encode enc x
    | Expr_eq x ->
      Bare.Encode.uint enc 19L;
      Expr_eq.encode enc x
    | Expr_app x ->
      Bare.Encode.uint enc 20L;
      Expr_app.encode enc x
    
    
    let pp out (self:t) : unit =
      match self with
      | Step_input x ->
        Format.fprintf out "(@[Step_input@ %a@])" Step_input.pp x
      | Step_unsat x ->
        Format.fprintf out "(@[Step_unsat@ %a@])" Step_unsat.pp x
      | Step_rup x ->
        Format.fprintf out "(@[Step_rup@ %a@])" Step_rup.pp x
      | Step_bridge_lit_expr x ->
        Format.fprintf out "(@[Step_bridge_lit_expr@ %a@])" Step_bridge_lit_expr.pp x
      | Step_cc x ->
        Format.fprintf out "(@[Step_cc@ %a@])" Step_cc.pp x
      | Step_preprocess x ->
        Format.fprintf out "(@[Step_preprocess@ %a@])" Step_preprocess.pp x
      | Step_clause_rw x ->
        Format.fprintf out "(@[Step_clause_rw@ %a@])" Step_clause_rw.pp x
      | Step_bool_tauto x ->
        Format.fprintf out "(@[Step_bool_tauto@ %a@])" Step_bool_tauto.pp x
      | Step_bool_c x ->
        Format.fprintf out "(@[Step_bool_c@ %a@])" Step_bool_c.pp x
      | Step_proof_p1 x ->
        Format.fprintf out "(@[Step_proof_p1@ %a@])" Step_proof_p1.pp x
      | Step_proof_r1 x ->
        Format.fprintf out "(@[Step_proof_r1@ %a@])" Step_proof_r1.pp x
      | Step_proof_res x ->
        Format.fprintf out "(@[Step_proof_res@ %a@])" Step_proof_res.pp x
      | Step_true x ->
        Format.fprintf out "(@[Step_true@ %a@])" Step_true.pp x
      | Fun_decl x ->
        Format.fprintf out "(@[Fun_decl@ %a@])" Fun_decl.pp x
      | Expr_def x ->
        Format.fprintf out "(@[Expr_def@ %a@])" Expr_def.pp x
      | Expr_bool x ->
        Format.fprintf out "(@[Expr_bool@ %a@])" Expr_bool.pp x
      | Expr_if x ->
        Format.fprintf out "(@[Expr_if@ %a@])" Expr_if.pp x
      | Expr_not x ->
        Format.fprintf out "(@[Expr_not@ %a@])" Expr_not.pp x
      | Expr_isa x ->
        Format.fprintf out "(@[Expr_isa@ %a@])" Expr_isa.pp x
      | Expr_eq x ->
        Format.fprintf out "(@[Expr_eq@ %a@])" Expr_eq.pp x
      | Expr_app x ->
        Format.fprintf out "(@[Expr_app@ %a@])" Expr_app.pp x
      
      
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
  
  let pp out (self:t) : unit =
    (fun out x ->
     begin
       Format.fprintf out "{ @[";
       Format.fprintf out "id=%a;@ " ID.pp x.id;
       Format.fprintf out "view=%a;@ " Step_view.pp x.view;
       Format.fprintf out "@]}";
     end) out self

end


