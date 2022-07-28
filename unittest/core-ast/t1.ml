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
let bool = Str_const.const store "Bool" ~ty:(type_ store)
let a = Str_const.const store "a" ~ty:bool
let a' = Str_const.const store "a" ~ty:bool
let b = Str_const.const store "b" ~ty:bool

let () =
  Fmt.printf "a: %a, b: %a, typeof(a): %a@." pp_debug a pp_debug b pp_debug
    (ty_exn a)

let () = assert (equal a a)
let () = assert (not (equal a b))
let ty_b2b = arrow store bool bool
let () = Fmt.printf "b2b: %a@." pp_debug ty_b2b
let p = Str_const.const store "p" ~ty:ty_b2b
let q = Str_const.const store "q" ~ty:ty_b2b
let pa = app store p a
let pb = app store p b
let qa = app store q a
let qb = app store q b
let () = Fmt.printf "p(a): %a@." pp_debug pa
let () = Fmt.printf "p(b): %a@." pp_debug pb
let () = Fmt.printf "q(a): %a@." pp_debug qa
let () = Fmt.printf "q(b): %a@." pp_debug qb
let () = assert (equal pa (app store p a))

(* *)

let ty_pa = ty_exn pa
let () = Fmt.printf "typeof(p a): %a@." pp_debug ty_pa

(* *)

let v_x = Var.make "x" bool
let v_y = Var.make "y" bool
let x = var store v_x
let y = var store v_y
let lxy_px = lam store v_x @@ lam store v_y @@ app store p x

let () =
  Fmt.printf "@[<v2>lxy_px: %a@ type: %a@]@." pp_debug lxy_px pp_debug
    (ty_exn lxy_px)

let () =
  let t = app_l store lxy_px [ a; b ] in
  Fmt.printf "@[<v2>lxy_px a b: %a@ type: %a@]@." pp_debug t pp_debug (ty_exn t)
