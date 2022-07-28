open Sidekick_core_logic

let store = Store.create ()
let t0 = Term.type_ store
let () = Fmt.printf "type0 : %a@." Term.pp_debug t0
let () = Fmt.printf "typeof(type0) : %a@." Term.pp_debug (Term.get_ty store t0)

let l =
  CCSeq.unfold (fun ty -> Some (ty, Term.get_ty store ty)) t0
  |> CCSeq.take 10 |> CCSeq.to_list

let () = Fmt.printf "type tower: %a@." (Fmt.Dump.list Term.pp_debug) l
let () = assert (Term.(equal (type_ store) (type_ store)))
let bool = Term.const store @@ Str_const.make "Bool" ~ty:(Term.type_ store)
let a = Term.const store @@ Str_const.make "a" ~ty:bool
let a' = Term.const store @@ Str_const.make "a" ~ty:bool
let b = Term.const store @@ Str_const.make "b" ~ty:bool

let () =
  Fmt.printf "a: %a, b: %a, typeof(a): %a@." Term.pp_debug a Term.pp_debug b
    Term.pp_debug (Term.ty_exn a)

let () = assert (Term.(equal a a))
let () = assert (not Term.(equal a b))
let ty_b2b = Term.arrow store bool bool
let () = Fmt.printf "b2b: %a@." Term.pp_debug ty_b2b
let p = Term.const store @@ Str_const.make "p" ~ty:ty_b2b
let q = Term.const store @@ Str_const.make "q" ~ty:ty_b2b
let pa = Term.app store p a
let pb = Term.app store p b
let qa = Term.app store q a
let qb = Term.app store q b
let () = Fmt.printf "p(a): %a@." Term.pp_debug pa
let () = Fmt.printf "p(b): %a@." Term.pp_debug pb
let () = Fmt.printf "q(a): %a@." Term.pp_debug qa
let () = Fmt.printf "q(b): %a@." Term.pp_debug qb
let () = assert (Term.(equal pa (app store p a)))

(* *)

let ty_pa = Term.ty_exn pa
let () = Fmt.printf "typeof(p a): %a@." Term.pp_debug ty_pa

(* *)

let v_x = Var.make "x" bool
let v_y = Var.make "y" bool
let x = Term.var store v_x
let y = Term.var store v_y
let lxy_px = Term.lam store v_x @@ Term.lam store v_y @@ Term.app store p x

let () =
  Fmt.printf "@[<v2>lxy_px: %a@ type: %a@]@." Term.pp_debug lxy_px Term.pp_debug
    (Term.ty_exn lxy_px)

let () =
  let t = Term.app_l store lxy_px [ a; b ] in
  Fmt.printf "@[<v2>lxy_px a b: %a@ type: %a@]@." Term.pp_debug t Term.pp_debug
    (Term.ty_exn t)
