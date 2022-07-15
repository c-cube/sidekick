module Fmt = CCFormat

exception Error of string

let () =
  Printexc.register_printer (function
    | Error msg -> Some ("internal error: " ^ msg)
    | _ -> None)

let errorf msg = Fmt.ksprintf msg ~f:(fun s -> raise (Error s))
