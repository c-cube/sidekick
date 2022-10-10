open Common_

let reset_line = "\x1b[2K\r"
let start = now ()

type t = unit -> unit

let tick (self : t) = self ()
let clear_line _ : unit = Printf.printf "%s%!" reset_line

let create () : t =
  let n = ref 0 in
  let syms = "|\\-/" in
  fun () ->
    let diff = now () -. start in
    incr n;
    (* TODO: print some core stats in the progress bar
       let n_cl = Solver.pp_stats
    *)
    (* limit frequency *)
    if float !n > 6. *. diff then (
      let sym = String.get syms (!n mod String.length syms) in
      Printf.printf "%s[%.2fs %c]" reset_line diff sym;
      n := 0;
      flush stdout
    )
