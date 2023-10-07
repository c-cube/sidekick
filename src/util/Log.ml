(** {1 Logging functions, real version} *)

let enabled = true (* NOTE: change here for 0-overhead? *)
let debug_level_ = ref 0
let set_debug l = debug_level_ := l
let get_debug () = !debug_level_
let debug_fmt_ = ref Format.err_formatter
let set_debug_out f = debug_fmt_ := f
let buf_ = Buffer.create 128
let buf_fmt_ = Format.formatter_of_buffer buf_
let start_ = Unix.gettimeofday ()

(* does the printing, inconditionally *)
let[@inline never] debug_real_ l k =
  k (fun fmt ->
      let now = Unix.gettimeofday () -. start_ in
      Buffer.clear buf_;
      let once_done _fmt =
        Format.fprintf _fmt "@]@?";
        let msg = Buffer.contents buf_ in
        (* forward to profiling *)
        if Profile.enabled () then Profile.message msg;
        Format.fprintf !debug_fmt_ "@[<2>@{<Blue>[%d|%.3f]@}@ %s@]@." l now msg
      in

      Format.fprintf buf_fmt_ "@[<2>";
      Format.kfprintf once_done buf_fmt_ fmt)

let[@inline] debugf l k = if enabled && l <= !debug_level_ then debug_real_ l k
let[@inline] debug l msg = debugf l (fun k -> k "%s" msg)
