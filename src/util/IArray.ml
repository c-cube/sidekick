(* This file is free software. See file "license" for more details. *)

type 'a t = 'a array

let empty = [||]
let is_empty a = Array.length a = 0
let length = Array.length
let singleton x = [| x |]
let doubleton x y = [| x; y |]
let make n x = Array.make n x
let init n f = Array.init n f
let sub = Array.sub
let get = Array.get
let unsafe_get = Array.unsafe_get

let set a n x =
  let a' = Array.copy a in
  a'.(n) <- x;
  a'

let map = Array.map
let mapi = Array.mapi

let append a b =
  let na = length a in
  Array.init
    (na + length b)
    (fun i ->
      if i < na then
        a.(i)
      else
        b.(i - na))

let iter = Array.iter
let iteri = Array.iteri
let fold = Array.fold_left

let foldi f acc a =
  let n = ref 0 in
  Array.fold_left
    (fun acc x ->
      let acc = f acc !n x in
      incr n;
      acc)
    acc a

exception ExitNow

let for_all p a =
  try
    Array.iter (fun x -> if not (p x) then raise ExitNow) a;
    true
  with ExitNow -> false

let exists p a =
  try
    Array.iter (fun x -> if p x then raise ExitNow) a;
    false
  with ExitNow -> true

(** {2 Conversions} *)

type 'a iter = ('a -> unit) -> unit
type 'a gen = unit -> 'a option

let of_list = Array.of_list
let to_list = Array.to_list

let of_list_map f l =
  match l with
  | [] -> empty
  | x :: _ ->
    let arr = make (List.length l) (f x) in
    List.iteri (fun i x -> Array.unsafe_set arr i (f x)) l;
    arr

let to_list_map f a = CCArray.fold_right (fun x acc -> f x :: acc) a []
let of_array_map = Array.map
let to_array_map = Array.map
let of_array_unsafe a = a (* careful with that axe, Eugene *)

let to_iter a k = iter k a

let to_iter_sub a i len k =
  if i < 0 || i + len > Array.length a then invalid_arg "IArray.iter_sub";
  for j = i to i + len - 1 do
    k (Array.unsafe_get a j)
  done

let of_iter s =
  let l = ref [] in
  s (fun x -> l := x :: !l);
  Array.of_list (List.rev !l)

(*$Q
  Q.(list int) (fun l -> \
    let g = Iter.of_list l in \
    of_iter g |> to_iter |> Iter.to_list = l)
*)

let rec gen_to_list_ acc g =
  match g () with
  | None -> List.rev acc
  | Some x -> gen_to_list_ (x :: acc) g

let of_gen g =
  let l = gen_to_list_ [] g in
  Array.of_list l

let to_gen a =
  let i = ref 0 in
  fun () ->
    if !i < Array.length a then (
      let x = a.(!i) in
      incr i;
      Some x
    ) else
      None

(*$Q
  Q.(list int) (fun l -> \
    let g = Gen.of_list l in \
    of_gen g |> to_gen |> Gen.to_list = l)
*)

(** {2 IO} *)

type 'a printer = Format.formatter -> 'a -> unit

let print ?(start = "[|") ?(stop = "|]") ?(sep = ";") pp_item out a =
  Format.pp_print_string out start;
  for k = 0 to Array.length a - 1 do
    if k > 0 then (
      Format.pp_print_string out sep;
      Format.pp_print_cut out ()
    );
    pp_item out a.(k)
  done;
  Format.pp_print_string out stop;
  ()

(** {2 Binary} *)

let equal = CCArray.equal
let compare = CCArray.compare
let for_all2 = CCArray.for_all2
let exists2 = CCArray.exists2

let map2 f a b =
  if length a <> length b then invalid_arg "map2";
  init (length a) (fun i -> f (unsafe_get a i) (unsafe_get b i))

let iter2 f a b =
  if length a <> length b then invalid_arg "iter2";
  for i = 0 to length a - 1 do
    f (unsafe_get a i) (unsafe_get b i)
  done

let iteri2 f a b =
  if length a <> length b then invalid_arg "iteri2";
  for i = 0 to length a - 1 do
    f i (unsafe_get a i) (unsafe_get b i)
  done

let fold2 f acc a b =
  if length a <> length b then invalid_arg "fold2";
  let rec aux acc i =
    if i = length a then
      acc
    else (
      let acc = f acc (unsafe_get a i) (unsafe_get b i) in
      aux acc (i + 1)
    )
  in
  aux acc 0
