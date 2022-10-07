type position = Position.t
type loc = Loc.t = { start: position; end_: position }

open struct
  let mk_loc = Loc.mk
end

type 'a with_loc = { view: 'a; loc: loc }

type term = term_view with_loc
(** Expressions *)

and term_view =
  | Var of string
  | Int of string
  | App of term * term list
  | Let of let_binding list * term
  | Lambda of var list * term
  | Pi of var list * term
  | Arrow of term list * term
  | Error_node of string

and let_binding = var * term

and var = { name: string; ty: term option }
(** Variable *)

type decl = decl_view with_loc
(** Declarations *)

(* TODO: axiom *)
and decl_view =
  | D_def of { name: string; args: var list; ty_ret: term option; rhs: term }
  | D_hash of string * term
  | D_theorem of { name: string; goal: term; proof: proof }

and proof = proof_view with_loc

and proof_view =
  | P_by of term
  | P_exact of term
  | P_steps of {
      steps: proof_step list;  (** intermediate steps *)
      ret: proof;  (** proof for the result *)
    }

and proof_step = proof_step_view with_loc
and proof_step_view = { name: string; goal: term; proof: proof }

open struct
  let mk_ ~loc view : _ with_loc = { loc; view }
end

let view (t : term) = t.view
let loc (t : term) = t.loc
let var ?ty name : var = { name; ty }
let mk_var ~loc v : term = mk_ ~loc (Var v)

let mk_app f args : term =
  if args = [] then
    f
  else (
    let loc = List.fold_left (fun loc a -> Loc.merge loc a.loc) f.loc args in
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
    let loc = Loc.merge loc bod.loc in
    mk_ ~loc (Let (bs, bod))
  )

let mk_error ~loc msg : term = mk_ ~loc (Error_node msg)

let decl_def ~loc ?ty_ret name args rhs : decl =
  mk_ ~loc @@ D_def { name; args; ty_ret; rhs }

let decl_hash ~loc s t : decl = mk_ ~loc @@ D_hash (s, t)

let decl_theorem ~loc name goal proof : decl =
  mk_ ~loc @@ D_theorem { name; goal; proof }

let proof_by ~loc t : proof = mk_ ~loc @@ P_by t
let proof_exact ~loc t : proof = mk_ ~loc @@ P_exact t
let proof_steps ~loc steps ret : proof = mk_ ~loc @@ P_steps { steps; ret }
let step ~loc name goal proof : proof_step = mk_ ~loc @@ { name; goal; proof }

(** Pretty print terms *)
let rec pp_term out (e : term) : unit =
  let pp = pp_term in
  let pp_sub out e =
    match e.view with
    | App _ | Arrow _ | Pi _ | Let _ | Lambda _ ->
      Fmt.fprintf out "(@[%a@])" pp e
    | Var _ | Error_node _ | Int _ -> pp out e
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
    let ppb out ((x, t) : let_binding) =
      Fmt.fprintf out "@[<2>%s :=@ %a@]" x.name pp t
    in
    Fmt.fprintf out "@[@[<2>let@ @[<hv>%a@]@] in@ %a@]"
      (Util.pp_list ~sep:" and " ppb)
      bs pp bod
  | Lambda (args, bod) ->
    Fmt.fprintf out "@[lam %a.@ %a@]" (Util.pp_list pp_tyvar) args pp_sub bod
  | Pi (args, bod) ->
    Fmt.fprintf out "@[pi %a.@ %a@]" (Util.pp_list pp_tyvar) args pp_sub bod

and pp_tyvar out (x : var) : unit =
  match x.ty with
  | None -> Fmt.string out x.name
  | Some ty -> Fmt.fprintf out "(@[%s : %a@])" x.name pp_term ty

let rec pp_proof out (p : proof) : unit =
  match p.view with
  | P_by t -> Fmt.fprintf out "@[by@ %a@]" pp_term t
  | P_exact t -> Fmt.fprintf out "@[exact@ %a@]" pp_term t
  | P_steps { steps; ret } ->
    Fmt.fprintf out "{@[%a;@ %a@]}"
      (Util.pp_list ~sep:";" pp_proof_step)
      steps pp_proof ret

and pp_proof_step out (step : proof_step) : unit =
  let s = step.view in
  Fmt.fprintf out "@[<2>have %s := %a@ proof %a@]" s.name pp_term s.goal
    pp_proof s.proof

let pp_decl out (d : decl) =
  match d.view with
  | D_def { name; args; ty_ret; rhs } ->
    let pp_tyret out () =
      match ty_ret with
      | None -> ()
      | Some ty -> Fmt.fprintf out " @[: %a@]" pp_term ty
    in
    Fmt.fprintf out "@[<2>def %s%a%a :=@ %a@];" name (Util.pp_list pp_tyvar)
      args pp_tyret () pp_term rhs
  | D_hash (name, t) -> Fmt.fprintf out "@[<2>#%s@ %a@];" name pp_term t
  | D_theorem { name; goal; proof } ->
    Fmt.fprintf out "@[<hv2>theorem %s :=@ %a@ @[<hv2>proof %a@]@];" name
      pp_term goal pp_proof proof
