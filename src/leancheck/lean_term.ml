module Level = Sidekick_cic_lib.Level

type binder = BD | BI | BS | BC

type t =
  | Sort of Level.t
  | BVar of int (* de Bruijn index only, no type *)
  | Const of string * Level.t list
  | App of t * t
  | Lam of binder * string * t * t (* binder, name, var_ty, body *)
  | Pi of binder * string * t * t

let dummy = Sort Level.one

let rec pp out = function
  | Sort l -> Fmt.fprintf out "Sort(%a)" Level.pp l
  | BVar i -> Fmt.fprintf out "BVar(%d)" i
  | Const (n, []) -> Fmt.string out n
  | Const (n, ls) ->
    Fmt.fprintf out "(%s %a)" n (Fmt.list ~sep:(Fmt.return " ") Level.pp) ls
  | App (f, a) -> Fmt.fprintf out "(%a %a)" pp f pp a
  | Lam (_, n, ty, body) ->
    Fmt.fprintf out "(fun (%s : %a). %a)" n pp ty pp body
  | Pi (_, n, ty, body) ->
    Fmt.fprintf out "(forall (%s : %a). %a)" n pp ty pp body
