
(** {1 Process Statements} *)

module Fmt = CCFormat
module Ast = Sidekick_base_term.Ast
module E = CCResult
module Loc = Locations
module Process = Process

module Proof = struct
  type t = Proof_default
  let default = Proof_default
end

type 'a or_error = ('a, string) CCResult.t

module Parse = struct
  let parse_chan_exn ?(filename="<no name>") ic =
    let lexbuf = Lexing.from_channel ic in
    Loc.set_file lexbuf filename;
    Parser.parse_list Lexer.token lexbuf

  let parse_chan ?filename ic =
    try Result.Ok (parse_chan_exn ?filename ic)
    with e -> Result.Error (Printexc.to_string e)

  let parse_file_exn file : Parse_ast.statement list =
    CCIO.with_in file (parse_chan_exn ~filename:file)

  let parse_file file =
    try Result.Ok (parse_file_exn file)
    with e -> Result.Error (Printexc.to_string e)

  let parse_file_exn ctx file : Ast.statement list =
    (* delegate parsing to [Tip_parser] *)
    parse_file_exn file
    |> CCList.flat_map (Typecheck.conv_statement ctx)

  let parse file =
    let ctx = Typecheck.Ctx.create () in
    try Result.Ok (parse_file_exn ctx file)
    with e -> Result.Error (Printexc.to_string e)

  let parse_stdin () =
    let ctx = Typecheck.Ctx.create () in
    try
      parse_chan_exn ~filename:"<stdin>" stdin
      |> CCList.flat_map (Typecheck.conv_statement ctx)
      |> CCResult.return
    with e -> Result.Error (Printexc.to_string e)
end

module Term_bool : sig
  open Sidekick_th_bool
  type 'a view = 'a Bool_intf.view

  type term = Sidekick_smt.Term.t

  include Bool_intf.BOOL_TERM
    with type t = term
     and type state = Sidekick_smt.Term.state

  val and_ : state -> term -> term -> term
  val or_ : state -> term -> term -> term
  val not_ : state -> term -> term
  val imply : state -> term -> term -> term
  val imply_a : state -> term IArray.t -> term -> term
  val imply_l : state -> term list -> term -> term
  val eq : state -> term -> term -> term
  val neq : state -> term -> term -> term
  val and_a : state -> term IArray.t -> term
  val and_l : state -> term list -> term
  val or_a : state -> term IArray.t -> term
  val or_l : state -> term list -> term
end = struct
  module ID = Sidekick_smt.ID
  module T = Sidekick_smt.Term
  module Ty = Sidekick_smt.Ty
  open Sidekick_smt.Solver_types

  open Bool_intf

  type term = T.t
  type t = T.t
  type state = T.state

  type 'a view = 'a Bool_intf.view

  exception Not_a_th_term

  let id_and = ID.make "and"
  let id_or = ID.make "or"
  let id_imply = ID.make "=>"

  let equal = T.equal
  let hash = T.hash

  let view_id cst_id args =
    if ID.equal cst_id id_and then (
      B_and args
    ) else if ID.equal cst_id id_or then (
      B_or args
    ) else if ID.equal cst_id id_imply && IArray.length args >= 2 then (
      (* conclusion is stored first *)
      let len = IArray.length args in
      B_imply (IArray.sub args 1 (len-1), IArray.get args 0)
    ) else (
      raise_notrace Not_a_th_term
    )

  let view_as_bool (t:T.t) : T.t view =
    match T.view t with
    | Not u -> B_not u
    | App_cst ({cst_id; _}, args) ->
      (try view_id cst_id args with Not_a_th_term -> B_atom t)
    | _ -> B_atom t

  module C = struct

    let get_ty _ _ = Ty.prop

    let abs ~self _a =
      match T.view self with
      | Not u -> u, false
      | _ -> self, true

    let eval id args =
      let module Value = Sidekick_smt.Value in
      match view_id id args with
      | B_not (V_bool b) -> Value.bool (not b)
      | B_and a when IArray.for_all Value.is_true a -> Value.true_
      | B_and a when IArray.exists Value.is_false a -> Value.false_
      | B_or a when IArray.exists Value.is_true a -> Value.true_
      | B_or a when IArray.for_all Value.is_false a -> Value.false_
      | B_imply (_, V_bool true) -> Value.true_
      | B_imply (a,_) when IArray.exists Value.is_false a -> Value.true_
      | B_imply (a,b) when IArray.for_all Value.is_bool a && Value.is_bool b -> Value.false_
      | B_atom v -> v
      | B_not _ | B_and _ | B_or _ | B_imply _
        -> Error.errorf "non boolean value in boolean connective"

    (* no congruence closure for boolean terms *)
    let relevant _id _ _ = false

    let mk_cst ?(do_cc=false) id : cst =
      {cst_id=id;
       cst_view=Cst_def {
           pp=None; abs; ty=get_ty; relevant; do_cc; eval=eval id; }; }

    let not = T.not_
    let and_ = mk_cst id_and
    let or_ = mk_cst id_or
    let imply = mk_cst id_imply
  end

  let as_id id (t:T.t) : T.t IArray.t option =
    match T.view t with
    | App_cst ({cst_id; _}, args) when ID.equal id cst_id -> Some args
    | _ -> None

  (* flatten terms of the given ID *)
  let flatten_id op sign (l:T.t list) : T.t list =
    CCList.flat_map
      (fun t -> match as_id op t with
         | Some args -> IArray.to_list args
         | None when (sign && T.is_true t) || (not sign && T.is_false t) ->
           [] (* idempotent *)
         | None -> [t])
      l

  let and_l st l =
    match flatten_id id_and true l with
    | [] -> T.true_ st
    | l when List.exists T.is_false l -> T.false_ st
    | [x] -> x
    | args -> T.app_cst st C.and_ (IArray.of_list args)

  let or_l st l =
    match flatten_id id_or false l with
    | [] -> T.false_ st
    | l when List.exists T.is_true l -> T.true_ st
    | [x] -> x
    | args -> T.app_cst st C.or_ (IArray.of_list args)

  let and_ st a b = and_l st [a;b]
  let or_ st a b = or_l st [a;b]
  let and_a st a = and_l st (IArray.to_list a)
  let or_a st a = or_l st (IArray.to_list a)
  let eq = T.eq
  let not_ = T.not_

  let neq st a b = not_ st @@ eq st a b

  let imply_a st xs y =
    if IArray.is_empty xs then y
    else T.app_cst st C.imply (IArray.append (IArray.singleton y) xs)

  let imply_l st xs y = match xs with
    | [] -> y
    | _ -> T.app_cst st C.imply (IArray.of_list @@ y :: xs)

  let imply st a b = imply_a st (IArray.singleton a) b

  let make st = function
    | B_atom t -> t
    | B_and l -> and_a st l
    | B_or l -> or_a st l
    | B_imply (a,b) -> imply_a st a b
    | B_not t -> not_ st t
end

module Term_distinct = struct
  open Sidekick_base_term

  let id_distinct = ID.make "distinct"

  let relevant _id _ _ = true
  let get_ty _ _ = Ty.prop
  let abs ~self _a = self, true

  module T = struct
    include Term
    let mk_eq = eq

    let as_distinct t : _ option =
      match view t with
      | App_cst ({cst_id;_}, args) when ID.equal cst_id id_distinct ->
        Some (IArray.to_seq args)
      | _ -> None
  end

  module Lit = Sidekick_smt.Lit

  let eval args =
    let module Value = Sidekick_smt.Value in
    Log.debugf 5
      (fun k->k "(@[distinct.eval@ %a@])" (Fmt.seq Value.pp) (IArray.to_seq args));
    if
      Iter.diagonal (IArray.to_seq args)
      |> Iter.for_all (fun (x,y) -> not @@ Value.equal x y)
    then Value.true_
    else Value.false_

  let c_distinct =
    {cst_id=id_distinct;
     cst_view=Cst_def {
         pp=None; abs; ty=get_ty; relevant; do_cc=true; eval; }; }

  let distinct st a =
    if IArray.length a <= 1
    then T.true_ st
    else T.app_cst st c_distinct a

  let distinct_l st = function
    | [] | [_] -> T.true_ st
    | xs -> distinct st (IArray.of_list xs)
end

module Term_ite = struct
  open Sidekick_base_term

  let[@inline] view_as_ite t = match Term.view t with
    | If (a,b,c) -> T_ite (a,b,c)
    | Bool b -> T_bool b
    | _ -> T_other t
end

module Solver = Sidekick_msat_solver.Solver

module Theories = struct
  module Th_cstor = Sidekick_th_cstor.Make(struct
      module Solver = Solver
      module T = Solver.A.Term

      let[@inline] view_as_cstor t = match view t with
        | App_cst (c, args) when Fun.do_cc
        | If (a,b,c) -> T_ite (a,b,c)
        | Bool b -> T_bool b
        | _ -> T_other t
      end

    end)
end

let parse = Parse.parse
let parse_stdin = Parse.parse_stdin
