(* This file is free software. See file "license" for more details. *)

type 'a t = 'a -> int

(* FNV hashing
   https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function
*)
let fnv_offset_basis = 0xcbf29ce484222325L
let fnv_prime = 0x100000001b3L

(* hash an integer *)
let hash_int_ n =
  let h = ref fnv_offset_basis in
  for k = 0 to 7 do
    (h := Int64.(mul !h fnv_prime));
    h := Int64.(logxor !h (of_int ((n lsr (k * 8)) land 0xff)))
  done;
  (* truncate back to int and remove sign *)
  Int64.to_int !h land max_int

let combine2 a b =
  let h = ref fnv_offset_basis in
  (* we only do one loop, where we mix bytes of [a] and [b], so as
     to simplify control flow *)
  for k = 0 to 7 do
    (h := Int64.(mul !h fnv_prime));
    (h := Int64.(logxor !h (of_int ((a lsr (k * 8)) land 0xff))));
    (h := Int64.(mul !h fnv_prime));
    h := Int64.(logxor !h (of_int ((b lsr (k * 8)) land 0xff)))
  done;
  Int64.to_int !h land max_int

let[@inline] combine f s x = combine2 s (f x)

let combine3 a b c =
  let h = ref fnv_offset_basis in
  (* we only do one loop, where we mix bytes of [a] [b] and [c], so as
     to simplify control flow *)
  for k = 0 to 7 do
    (h := Int64.(mul !h fnv_prime));
    (h := Int64.(logxor !h (of_int ((a lsr (k * 8)) land 0xff))));
    (h := Int64.(mul !h fnv_prime));
    (h := Int64.(logxor !h (of_int ((b lsr (k * 8)) land 0xff))));
    (h := Int64.(mul !h fnv_prime));
    h := Int64.(logxor !h (of_int ((c lsr (k * 8)) land 0xff)))
  done;
  Int64.to_int !h land max_int

let combine4 a b c d =
  let h = ref fnv_offset_basis in
  for k = 0 to 7 do
    (h := Int64.(mul !h fnv_prime));
    (h := Int64.(logxor !h (of_int ((a lsr (k * 8)) land 0xff))));
    (h := Int64.(mul !h fnv_prime));
    (h := Int64.(logxor !h (of_int ((b lsr (k * 8)) land 0xff))));
    (h := Int64.(mul !h fnv_prime));
    (h := Int64.(logxor !h (of_int ((c lsr (k * 8)) land 0xff))));
    (h := Int64.(mul !h fnv_prime));
    h := Int64.(logxor !h (of_int ((d lsr (k * 8)) land 0xff)))
  done;
  Int64.to_int !h land max_int

let[@inline] pair f g (x, y) = combine2 (f x) (g y)

let opt f = function
  | None -> 42
  | Some x -> combine2 43 (f x)

let[@inline] int x = hash_int_ x
let h_true_ = hash_int_ 1
let h_false_ = hash_int_ 0

let[@inline] bool b =
  if b then
    h_true_
  else
    h_false_

let list f l = List.fold_left (combine f) 0x42 l
let array f = Array.fold_left (combine f) 0x43
let iarray f = CCArray.fold (combine f) 0x44
let string : string t = Hashtbl.hash

let seq f seq =
  let h = ref 0x43 in
  seq (fun x -> h := combine f !h x);
  !h

let poly x = Hashtbl.hash x
