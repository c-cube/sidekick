type tag = string

module type S = sig
  val get_entry : Entry_id.t -> tag * Ser_value.t
  val iter_all : (Entry_id.t -> tag:tag -> Ser_value.t -> unit) -> unit
end

type t = (module S)

let get_entry_exn (module S : S) id = S.get_entry id

let get_entry (module S : S) id : _ option =
  try Some (S.get_entry id) with Not_found -> None

let iter_all (module S : S) f : unit = S.iter_all f

let decode_bencode_entry_ =
  Ser_decode.(
    let+ id, tag, view = tup3 int string any in
    id, tag, view)

let is_whitespace_ = function
  | ' ' | '\t' | '\n' -> true
  | _ -> false

let of_string_using_bencode (str : string) : t =
  (module struct
    let iter_all f =
      let i = ref 0 in
      while !i < String.length str do
        while !i < String.length str && is_whitespace_ str.[!i] do
          incr i
        done;
        if !i < String.length str then (
          match Sidekick_bencode.Decode.of_string ~idx:!i str with
          | None -> i := String.length str
          | Some (len, b) ->
            i := !i + len;
            (match Ser_decode.run decode_bencode_entry_ b with
            | Error err ->
              Error.errorf "cannot decode string entry: %a" Ser_decode.Error.pp
                err
            | Ok (id, tag, v) -> f id ~tag v)
        )
      done

    let get_entry id : tag * Ser_value.t =
      match Sidekick_bencode.Decode.of_string str ~idx:id with
      | None -> Error.errorf "invalid offset %d" id
      | Some (_len, b) ->
        (match Ser_decode.run decode_bencode_entry_ b with
        | Error err ->
          Error.errorf "cannot decode string entry: %a" Ser_decode.Error.pp err
        | Ok (_id, tag, v) ->
          assert (id = _id);
          tag, v)
  end)
