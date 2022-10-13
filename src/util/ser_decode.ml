open struct
  module Error_ = Error
  module Fmt = CCFormat
  module V = Ser_value
end

module Error = struct
  type t = { msg: string; v: V.t; subs: t list }

  let mk ?(subs = []) msg v : t = { msg; v; subs }
  let of_string s v : t = mk s v

  let pp out (self : t) =
    let rec pp out self =
      Fmt.fprintf out "@[<v2>@[<2>%s@ in value %a@]" self.msg V.pp self.v;
      List.iter
        (fun s -> Fmt.fprintf out "@ @[<2>sub-error:@ %a@]" pp s)
        self.subs;
      Fmt.fprintf out "@]"
    in
    Fmt.fprintf out "@[<2>Ser_decode.error:@ %a@]" pp self

  let to_string = Fmt.to_string pp
end

exception Fail of Error.t

type 'a t = { deser: V.t -> 'a } [@@unboxed]

let[@inline] fail_ msg v = raise_notrace (Fail (Error.mk msg v))
let[@inline] fail_e e = raise_notrace (Fail e)
let fail_err e = { deser = (fun _ -> fail_e e) }
let return x = { deser = (fun _ -> x) }
let fail s = { deser = (fun v -> fail_ s v) }
let failf fmt = Fmt.kasprintf fail fmt
let delay f = { deser = (fun v -> (f ()).deser v) }

let return_result = function
  | Ok x -> return x
  | Error s -> fail s

let return_result_err = function
  | Ok x -> return x
  | Error e -> fail_err e

let unwrap_opt msg = function
  | Some x -> return x
  | None -> fail msg

let any = { deser = (fun v -> v) }

let bool =
  {
    deser =
      (function
      | V.Bool b -> b
      | V.Int 1 -> true
      | V.Int 0 -> false
      | v -> fail_ "expected bool" v);
  }

let int =
  {
    deser =
      (function
      | V.Int i -> i
      | v -> fail_ "expected int" v);
  }

let string =
  {
    deser =
      (function
      | V.Str s | V.Bytes s -> s
      | v -> fail_ "expected string" v);
  }

let reflect dec v =
  {
    deser =
      (fun _ ->
        match dec.deser v with
        | x -> Ok x
        | exception Fail e -> Error e);
  }

let reflect_or_fail dec v = { deser = (fun _ -> dec.deser v) }

let list d =
  {
    deser =
      (function
      | V.List l -> List.map (fun x -> d.deser x) l
      | v -> fail_ "expected list" v);
  }

let dict_field name d =
  {
    deser =
      (function
      | V.Dict m as v ->
        (match Util.Str_map.find_opt name m with
        | None -> fail_ (Printf.sprintf "did not find key %S" name) v
        | Some x -> d.deser x)
      | v -> fail_ "expected dict" v);
  }

let dict_field_opt name d =
  {
    deser =
      (function
      | V.Dict m ->
        (match Util.Str_map.find_opt name m with
        | None -> None
        | Some x -> Some (d.deser x))
      | v -> fail_ "expected dict" v);
  }

let both a b =
  {
    deser =
      (fun v ->
        let xa = a.deser v in
        let xb = b.deser v in
        xa, xb);
  }

let ( >>= ) d f =
  {
    deser =
      (fun v ->
        let x = d.deser v in
        (f x).deser v);
  }

let ( >|= ) d f =
  {
    deser =
      (fun v ->
        let x = d.deser v in
        f x);
  }

let try_l l =
  {
    deser =
      (fun v ->
        let subs = ref [] in
        match
          CCList.find_map
            (fun d ->
              match d.deser v with
              | x -> Some x
              | exception Fail err ->
                subs := err :: !subs;
                None)
            l
        with
        | Some x -> x
        | None -> fail_e (Error.mk "all decoders failed" v ~subs:!subs));
  }

module Infix = struct
  let ( >>= ) = ( >>= )
  let ( >|= ) = ( >|= )
  let ( and+ ) = both
  let ( and* ) = both
  let ( let+ ) = ( >|= )
  let ( let* ) = ( >>= )
end

include Infix

let dict_field_or default name d =
  let+ r = dict_field_opt name d in
  match r with
  | Some r -> r
  | None -> default

let tup2 d1 d2 =
  let* l = list any in
  match l with
  | [ x1; x2 ] ->
    let+ x1 = reflect_or_fail d1 x1 and+ x2 = reflect_or_fail d2 x2 in
    x1, x2
  | _ -> fail "expected a pair"

let tup3 d1 d2 d3 =
  let* l = list any in
  match l with
  | [ x1; x2; x3 ] ->
    let+ x1 = reflect_or_fail d1 x1
    and+ x2 = reflect_or_fail d2 x2
    and+ x3 = reflect_or_fail d3 x3 in
    x1, x2, x3
  | _ -> fail "expected a triple"

let tup4 d1 d2 d3 d4 =
  let* l = list any in
  match l with
  | [ x1; x2; x3; x4 ] ->
    let+ x1 = reflect_or_fail d1 x1
    and+ x2 = reflect_or_fail d2 x2
    and+ x3 = reflect_or_fail d3 x3
    and+ x4 = reflect_or_fail d4 x4 in
    x1, x2, x3, x4
  | _ -> fail "expected a 4-tuple"

let run d v = try Ok (d.deser v) with Fail err -> Error err

let run_exn d v =
  try d.deser v
  with Fail err ->
    Error_.errorf "ser_decode: failed to decode:@ %a" Error.pp err
