

module type ARG = sig
  (** terms *)
  module T : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int
    val pp : t Fmt.printer
  end

  type tag
end

module Pred : sig
  type t = Lt | Leq | Geq | Gt | Neq | Eq

  val neg : t -> t
  val pp : t Fmt.printer
  val to_string : t -> string
end = struct
  type t = Lt | Leq | Geq | Gt | Neq | Eq
  let to_string = function
    | Lt -> "<"
    | Leq -> "<="
    | Eq -> "="
    | Neq -> "!="
    | Gt -> ">"
    | Geq -> ">="

  let neg = function
    | Leq -> Gt
    | Lt -> Geq
    | Eq -> Neq
    | Neq -> Eq
    | Geq -> Lt
    | Gt -> Leq

  let pp out p = Fmt.string out (to_string p)
end

module type S = sig
  module A : ARG

  type t

  type expr = A.T.t

  module LE : sig
    type t

    val const : Q.t -> t
    val var : expr -> t

    module Infix : sig
      val (+) : t -> t -> t
      val (-) : t -> t -> t
      val ( * ) : Q.t -> t -> t
    end
    include module type of Infix

    val pp : t Fmt.printer
  end

  (** {3 Arithmetic constraint} *)
  module Constr : sig
    type t = {
      pred: Pred.t;
      le: LE.t;
      tag: A.tag option;
    }

    val mk : ?tag:A.tag -> Pred.t -> LE.t -> LE.t -> t

    val pp : t Fmt.printer
  end

  val create : unit -> t

  val assert_c : t -> Constr.t -> unit

  type res =
    | Sat
    | Unsat of A.tag list

  val solve : t -> res
end

module Make(A : ARG)
  : S with module A = A
= struct
  module A = A
  module T = A.T

  module T_set = CCSet.Make(A.T)
  module T_map = CCMap.Make(A.T)

  type expr = A.T.t

  module LE = struct
    module M = T_map

    type t = {
      le: Q.t M.t;
      const: Q.t;
    }

    let const x : t = {const=x; le=M.empty}
    let var x : t = {const=Q.zero; le=M.singleton x Q.one}

    let (+) a b : t =
      {const = Q.(a.const + b.const);
       le=M.merge_safe a.le b.le
           ~f:(fun _ -> function
               | `Left x | `Right x -> Some x
               | `Both (x,y) ->
                 let z = Q.(x + y) in
                 if Q.sign z = 0 then None else Some z)
      }

    let (-) a b : t =
      {const = Q.(a.const - b.const);
       le=M.merge_safe a.le b.le
           ~f:(fun _ -> function
               | `Left x -> Some x
               | `Right x -> Some (Q.neg x)
               | `Both (x,y) ->
                 let z = Q.(x - y) in
                 if Q.sign z = 0 then None else Some z)
      }

    let ( * ) x a : t =
      if Q.sign x = 0 then const Q.zero
      else (
        {const=Q.( a.const * x );
         le=M.map (fun y -> Q.(x * y)) a.le
        }
      )

    module Infix = struct
      let (+) = (+)
      let (-) = (-)
      let ( * ) = ( * )
    end

    let vars self = T_map.keys self.le

    let pp out (self:t) : unit =
      let pp_pair out (e,q) =
        if Q.equal Q.one q then T.pp out e
        else Fmt.fprintf out "%a * %a" Q.pp_print q T.pp e
      in
      Fmt.fprintf out "(@[%a@ + %a@])"
        Q.pp_print self.const (Util.pp_iter ~sep:" + " pp_pair) (M.to_iter self.le)
  end

  module Constr = struct
    type t = {
      pred: Pred.t;
      le: LE.t;
      tag: A.tag option;
    }

    let pp out (c:t) : unit =
      Fmt.fprintf out "(@[constr@ :le %a@ :pred %s 0@])"
        LE.pp c.le (Pred.to_string c.pred)


    let mk ?tag pred l1 l2 : t =
      {pred; tag; le=LE.(l1 - l2); }
  end

  type t = {
    mutable cs: Constr.t list;
    mutable all_vars: T_set.t;
  }

  let create () : t = {
    cs=[];
    all_vars=T_set.empty;
  }

  let assert_c (self:t) c : unit =
    self.cs <- c :: self.cs;
    self.all_vars <- c.Constr.le |> LE.vars |> T_set.add_iter self.all_vars;
    ()

  (* TODO: be able to provide a model for SAT *)
  type res =
    | Sat
    | Unsat of A.tag list

  let solve (self:t) : res =
    Log.debugf 5
      (fun k->k"(@[FM.solve@ %a@])" (Util.pp_list Constr.pp) self.cs);
    assert false
end

