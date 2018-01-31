
(* This file is free software. See file "license" for more details. *)

(** {1 Util} *)

module Fmt = CCFormat

type 'a printer = 'a CCFormat.printer

let pp_sep sep out () = Format.fprintf out "%s@," sep

let pp_list ?(sep=" ") pp out l =
  Fmt.list ~sep:(pp_sep sep) pp out l

let pp_pair ?(sep=" ") pp1 pp2 out t =
  Fmt.pair ~sep:(pp_sep sep) pp1 pp2 out t

let pp_array ?(sep=" ") pp out l =
  Fmt.array ~sep:(pp_sep sep) pp out l

let pp_iarray ?(sep=" ") pp out a =
  Fmt.seq ~sep:(pp_sep sep) pp out (IArray.to_seq a)

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some ("internal error: " ^ msg)
      | _ -> None)

let errorf msg = Fmt.ksprintf msg ~f:(fun s -> raise (Error s))
