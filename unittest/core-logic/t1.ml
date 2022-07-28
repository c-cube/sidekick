open Sidekick_core_logic

let store = Store.create ()
let type_ = Term.type_ store
let () = Fmt.printf "type0 : %a@." Term.pp_debug type_
let () = Fmt.printf "typeof(type0) : %a@." Term.pp_debug (Term.ty type_)

let l =
  CCSeq.unfold (fun ty -> Some (ty, Term.ty ty)) type_
  |> CCSeq.take 5 |> CCSeq.to_list

let () = Fmt.printf "type tower: %a@." (Fmt.Dump.list Term.pp_debug) l
let () = assert (Term.(equal (type_ store) (type_ store)))
let bool = Term.const store @@ Str_const.make "Bool" ~ty:(Term.type_ store)
let a = Term.const store @@ Str_const.make "a" ~ty:bool
let a' = Term.const store @@ Str_const.make "a" ~ty:bool
let b = Term.const store @@ Str_const.make "b" ~ty:bool

let () =
  Fmt.printf "a: %a, b: %a, typeof(a): %a@." Term.pp_debug a Term.pp_debug b
    Term.pp_debug (Term.ty a)

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

let ty_pa = Term.ty pa
let () = Fmt.printf "typeof(p a): %a@." Term.pp_debug ty_pa

(* *)

let v_x = Var.make "x" bool
let v_y = Var.make "y" bool
let x = Term.var store v_x
let y = Term.var store v_y
let lxy_px = Term.lam store v_x @@ Term.lam store v_y @@ Term.app store p x

let () =
  Fmt.printf "@[<v2>lxy_px: %a@ type: %a@ type of type: %a@]@." Term.pp_debug
    lxy_px Term.pp_debug (Term.ty lxy_px) Term.pp_debug
    (Term.ty @@ Term.ty lxy_px)

let () =
  let t = Term.app_l store lxy_px [ a; b ] in
  Fmt.printf "@[<v2>lxy_px a b: %a@ type: %a@]@." Term.pp_debug t Term.pp_debug
    (Term.ty t)

(* *)

let tau = Term.const store @@ Str_const.make "tau" ~ty:type_

let f_eq =
  let vAlpha = Var.make "Alpha" type_ in
  let tAlpha = Term.var store vAlpha in
  Term.const store
  @@ Str_const.make "="
       ~ty:Term.(pi store vAlpha @@ arrow_l store [ tAlpha; tAlpha ] bool)

let () =
  Fmt.printf "@[<v2>(=): %a@ type: %a@]@." Term.pp_debug f_eq Term.pp_debug
    (Term.ty f_eq)

let app_eq store x y = Term.app_l store f_eq [ Term.ty x; x; y ]

let p2 =
  Term.const store
  @@ Str_const.make "p2" ~ty:Term.(arrow_l store [ tau; tau ] bool)

let () =
  Fmt.printf "@[<v2>p2: %a@ type: %a@]@." Term.pp_debug p2 Term.pp_debug
    (Term.ty p2)

let t2 =
  let vx = Var.make "x" tau in
  let vy = Var.make "y" tau in
  let tX = Term.var store vx in
  let tY = Term.var store vy in
  Term.(
    let t1 = lam store vx @@ lam store vy @@ app_l store p2 [ tX; tY ]
    and t2 = app store f_eq tau in
    app_eq store t1 t2)

let () =
  Fmt.printf "@[<v2>t2: %a@ type: %a@]@." Term.pp_debug t2 Term.pp_debug
    (Term.ty t2)

(* a bit of dependent types *)

let nat = Term.const store @@ Str_const.make "nat" ~ty:type_

let f_vec =
  let v_A = Var.make "A" type_ in
  let v_n = Var.make "n" nat in
  Term.const store
  @@ Str_const.make "vec" ~ty:Term.(pi store v_A @@ pi store v_n @@ type_ store)

let () =
  Fmt.printf "@[<v2>f_vec: %a@ type: %a@ type of type: %a@]@." Term.pp_debug
    f_vec Term.pp_debug (Term.ty f_vec) Term.pp_debug
    (Term.ty @@ Term.ty f_vec)
