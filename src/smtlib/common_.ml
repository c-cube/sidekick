(** Current timestamp *)
let now () : float = Unix.gettimeofday ()

(** Timestamp at the beginning of the program *)
let time_start = now ()

(** write to file, possibly with compression *)
let with_file_out (file : string) (f : out_channel -> 'a) : 'a =
  if Filename.extension file = ".gz" then (
    let p =
      Unix.open_process_out
        (Printf.sprintf "gzip -c - > \"%s\"" (String.escaped file))
    in
    CCFun.finally1 ~h:(fun () -> Unix.close_process_out p) f p
  ) else
    CCIO.with_out file f
