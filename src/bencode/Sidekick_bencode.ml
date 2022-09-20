module V = Ser_value

type t = Ser_value.t

module Encode = struct
  let to_buffer (buf : Buffer.t) (v : t) : unit =
    let[@inline] char c = Buffer.add_char buf c in
    let[@inline] str s = Buffer.add_string buf s in
    let[@inline] int i = Printf.bprintf buf "%d" i in

    let rec enc_v (v : t) : unit =
      match v with
      | Int i ->
        char 'i';
        int i;
        char 'e'
      | Bool true -> str "i1e"
      | Bool false -> str "i0e"
      | Str s | Bytes s ->
        int (String.length s);
        char ':';
        str s
      | List l ->
        char 'l';
        List.iter (fun v -> enc_v v) l;
        char 'e'
      | Dict l ->
        char 'd';
        Util.Str_map.iter
          (fun k v ->
            enc_v (V.string k);
            enc_v v)
          l;
        char 'e'
    in
    enc_v v

  let to_string v : string =
    let buf = Buffer.create 16 in
    to_buffer buf v;
    Buffer.contents buf
end

module Decode = struct
  exception Fail

  let of_string s =
    let i = ref 0 in

    let[@inline] check_not_eof () =
      if !i >= String.length s then raise_notrace Fail
    in

    let rec top () : t =
      check_not_eof ();
      match String.unsafe_get s !i with
      | 'l' ->
        incr i;
        read_list []
      | 'd' ->
        incr i;
        read_map Util.Str_map.empty
      | 'i' ->
        incr i;
        let n = read_int 'e' true 0 in
        V.int n
      | '0' .. '9' -> V.string (parse_str_len ())
      | _ -> raise_notrace Fail
    (* read integer until char [stop] is met, consume [stop], return int *)
    and read_int stop sign n : int =
      check_not_eof ();
      match String.unsafe_get s !i with
      | c when c == stop ->
        incr i;
        if sign then
          n
        else
          -n
      | '-' when stop == 'e' && sign && n = 0 ->
        incr i;
        read_int stop false n
      | '0' .. '9' as c ->
        incr i;
        read_int stop sign (Char.code c - Char.code '0' + (10 * n))
      | _ -> raise_notrace Fail
    and parse_str_len () : string =
      let n = read_int ':' true 0 in
      if !i + n > String.length s then raise_notrace Fail;
      let s = String.sub s !i n in
      i := !i + n;
      s
    and read_list acc =
      check_not_eof ();
      match String.unsafe_get s !i with
      | 'e' ->
        incr i;
        V.list (List.rev acc)
      | _ ->
        let x = top () in
        read_list (x :: acc)
    and read_map acc =
      check_not_eof ();
      match String.unsafe_get s !i with
      | 'e' ->
        incr i;
        V.dict acc
      | _ ->
        let k = parse_str_len () in
        let v = top () in
        read_map (Util.Str_map.add k v acc)
    in

    try Some (top ()) with Fail -> None

  let of_string_exn s =
    match of_string s with
    | Some x -> x
    | None -> failwith "bencode.decode: invalid string"
end
