(* This file is free software. See file "license" for more details. *)

(** {1 Util} *)

module Fmt = CCFormat

type 'a printer = 'a CCFormat.printer

let pp_sep sep out () = Format.fprintf out "%s@," sep
let pp_list ?(sep = " ") pp out l = Fmt.list ~sep:(pp_sep sep) pp out l
let pp_iter ?(sep = " ") pp out l = Fmt.iter ~sep:(pp_sep sep) pp out l

let pp_pair ?(sep = " ") pp1 pp2 out t =
  Fmt.pair ~sep:(pp_sep sep) pp1 pp2 out t

let pp_array ?(sep = " ") pp out l = Fmt.array ~sep:(pp_sep sep) pp out l
let flat_map_l_arr f l = CCList.flat_map (fun x -> CCArray.to_list @@ f x) l

let array_iteri2 ~f a b =
  let open Array in
  if length a <> length b then invalid_arg "iteri2";
  for i = 0 to length a - 1 do
    f i (unsafe_get a i) (unsafe_get b i)
  done

let array_of_list_map f l =
  match l with
  | [] -> [||]
  | x :: tl ->
    let arr = Array.make (List.length tl + 1) (f x) in
    List.iteri (fun i y -> arr.(i + 1) <- f y) tl;
    arr

let array_to_list_map f arr =
  CCList.init (Array.length arr) (fun i -> f arr.(i))

let lazy_map f x =
  lazy
    (let (lazy x) = x in
     f x)

let lazy_map2 f x y =
  lazy
    (let (lazy x) = x and (lazy y) = y in
     f x y)

let setup_gc () =
  let g = Gc.get () in
  Gc.set
    {
      g with
      Gc.space_overhead = 3_000;
      (* major gc *)
      max_overhead = 10_000;
      (* compaction *)
      minor_heap_size = 500_000 (* ×8 to obtain bytes on 64 bits -->  *);
    }

module Int_set = CCSet.Make (CCInt)
module Int_map = CCMap.Make (CCInt)
module Int_tbl = CCHashtbl.Make (CCInt)
module Str_tbl = CCHashtbl.Make (CCString)
module Str_map = CCMap.Make (CCString)
