open Sidekick_core_ast

let store = Store.create ()
let t0 = type_ store
let () = Fmt.printf "type0 : %a@." pp_debug t0
let () = Fmt.printf "typeof(type0) : %a@." pp_debug (get_ty store t0)

let l =
  CCSeq.unfold (fun ty -> Some (ty, get_ty store ty)) t0
  |> CCSeq.take 10 |> CCSeq.to_list

let () = Fmt.printf "type tower: %a@." (Fmt.Dump.list pp_debug) l
let () = assert (equal (type_ store) (type_ store))
