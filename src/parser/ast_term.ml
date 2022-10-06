module Pos = Parser_comb.Position

type position = Pos.t
type loc = { start: position; end_: position }

let mk_loc ~start ~end_ : loc = { start; end_ }

let pp_loc out (loc : loc) =
  Fmt.fprintf out "%a - %a" Pos.pp loc.start Pos.pp loc.end_

let loc_merge a b : loc =
  { start = Pos.min a.start b.start; end_ = Pos.max a.end_ b.end_ }

type term = { view: term_view; loc: loc }
(** Expressions *)

and term_view =
  | Var of string
  | Int of string
  | App of term * term list
  | Let of (var * term) list * term
  | Lambda of var list * term
  | Pi of var list * term
  | Arrow of term list * term
  | Error_node of string

and var = { name: string; ty: term option }
(** Variable *)

open struct
  let mk_ ~loc view : term = { loc; view }
end

let view (t : term) = t.view
let loc (t : term) = t.loc
let var ?ty name : var = { name; ty }
let mk_var ~loc v : term = mk_ ~loc (Var v)

let mk_app f args : term =
  if args = [] then
    f
  else (
    let loc = List.fold_left (fun loc a -> loc_merge loc a.loc) f.loc args in
    mk_ ~loc (App (f, args))
  )

let mk_arrow ~loc args ret : term =
  if args = [] then
    ret
  else
    mk_ ~loc (Arrow (args, ret))

let mk_lam ~loc args bod : term =
  if args = [] then
    bod
  else
    mk_ ~loc (Lambda (args, bod))

let mk_int ~loc x : term = mk_ ~loc (Int x)

let mk_pi ~loc args bod : term =
  if args = [] then
    bod
  else
    mk_ ~loc (Pi (args, bod))

let mk_let ~loc bs bod : term =
  if bs = [] then
    bod
  else (
    let loc = loc_merge loc bod.loc in
    mk_ ~loc (Let (bs, bod))
  )

let mk_error ~loc msg : term = mk_ ~loc (Error_node msg)

(** Pretty print terms *)
let rec pp_term out (e : term) : unit =
  let pp = pp_term in
  let pp_sub out e =
    match e.view with
    | App _ | Arrow _ | Pi _ | Let _ | Lambda _ ->
      Fmt.fprintf out "(@[%a@])" pp e
    | Var _ | Error_node _ | Int _ -> pp out e
  in

  let pp_tyvar out x =
    match x.ty with
    | None -> Fmt.string out x.name
    | Some ty -> Fmt.fprintf out "(@[%s : %a@])" x.name pp ty
  in

  match e.view with
  | Var v -> Fmt.string out v
  | Error_node msg -> Fmt.fprintf out "<error %s>" msg
  | Int i -> Fmt.string out i
  | App (f, args) ->
    Fmt.fprintf out "@[%a@ %a@]" pp_sub f (Util.pp_list pp_sub) args
  | Arrow (args, ret) ->
    Fmt.fprintf out "@[%a -> %a@]"
      (Util.pp_list ~sep:" -> " pp_sub)
      args pp_sub ret
  | Let (bs, bod) ->
    let ppb out (x, t) = Fmt.fprintf out "@[<2>%s :=@ %a@]" x.name pp t in
    Fmt.fprintf out "@[@[<2>let@ %a@] in@ %a@]"
      (Util.pp_list ~sep:"and" ppb)
      bs pp_sub bod
  | Lambda (args, bod) ->
    Fmt.fprintf out "@[lam %a.@ %a@]" (Util.pp_list pp_tyvar) args pp_sub bod
  | Pi (args, bod) ->
    Fmt.fprintf out "@[pi %a.@ %a@]" (Util.pp_list pp_tyvar) args pp_sub bod
