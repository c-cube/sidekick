type ('f, 't, 'ts) t =
  | Bool of bool
  | App_fun of 'f * 'ts
  | App_ho of 't * 't
  | If of 't * 't * 't
  | Eq of 't * 't
  | Not of 't
  | Opaque of 't
(* do not enter *)

let[@inline] map_view ~f_f ~f_t ~f_ts (v : _ t) : _ t =
  match v with
  | Bool b -> Bool b
  | App_fun (f, args) -> App_fun (f_f f, f_ts args)
  | App_ho (f, a) -> App_ho (f_t f, f_t a)
  | Not t -> Not (f_t t)
  | If (a, b, c) -> If (f_t a, f_t b, f_t c)
  | Eq (a, b) -> Eq (f_t a, f_t b)
  | Opaque t -> Opaque (f_t t)

let[@inline] iter_view ~f_f ~f_t ~f_ts (v : _ t) : unit =
  match v with
  | Bool _ -> ()
  | App_fun (f, args) ->
    f_f f;
    f_ts args
  | App_ho (f, a) ->
    f_t f;
    f_t a
  | Not t -> f_t t
  | If (a, b, c) ->
    f_t a;
    f_t b;
    f_t c
  | Eq (a, b) ->
    f_t a;
    f_t b
  | Opaque t -> f_t t
