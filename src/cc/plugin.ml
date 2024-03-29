open Types_
open Sigs_plugin

module type EXTENDED_PLUGIN_BUILDER = sig
  include MONOID_PLUGIN_BUILDER

  val mem : t -> E_node.t -> bool
  (** Does the CC.E_node.t have a monoid value? *)

  val get : t -> E_node.t -> M.t option
  (** Get monoid value for this CC.E_node.t, if any *)

  val iter_all : t -> (CC.repr * M.t) Iter.t

  include Sidekick_sigs.BACKTRACKABLE0 with type t := t
  include Sidekick_sigs.PRINT with type t := t
end

module Make (M : MONOID_PLUGIN_ARG) :
  EXTENDED_PLUGIN_BUILDER with module M = M = struct
  module M = M
  module Cls_tbl = Backtrackable_tbl.Make (E_node)

  module type DYN_PL_FOR_M = DYN_MONOID_PLUGIN with module M = M

  type t = (module DYN_PL_FOR_M)

  module Make (A : sig
    val size : int option
    val cc : CC.t
  end) : DYN_PL_FOR_M = struct
    module M = M
    module CC = CC
    open A

    (* plugin's state *)
    let plugin_st = M.create cc

    (* repr -> value for the class *)
    let values : M.t Cls_tbl.t = Cls_tbl.create ?size ()

    (* bit in CC to filter out quickly classes without value *)
    let field_has_value : CC.bitfield =
      CC.allocate_bitfield ~descr:("monoid." ^ M.name ^ ".has-value") cc

    let push_level () = Cls_tbl.push_level values
    let pop_levels n = Cls_tbl.pop_levels values n
    let n_levels () = Cls_tbl.n_levels values

    let mem n =
      let res = CC.get_bitfield cc field_has_value n in
      assert (
        if res then
          Cls_tbl.mem values n
        else
          true);
      res

    let get n =
      if CC.get_bitfield cc field_has_value n then
        Cls_tbl.get values n
      else
        None

    let on_new_term cc n (t : Term.t) : CC.Handler_action.t list =
      (*Log.debugf 50 (fun k->k "(@[monoid[%s].on-new-term.try@ %a@])" M.name N.pp n);*)
      let acts = ref [] in
      let maybe_m, l = M.of_term cc plugin_st n t in
      (match maybe_m with
      | Some v ->
        Log.debugf 20 (fun k ->
            k "(@[monoid[%s].on-new-term@ :n %a@ :value %a@])" M.name E_node.pp
              n M.pp v);
        CC.set_bitfield cc field_has_value true n;
        Cls_tbl.add values n v
      | None -> ());
      List.iter
        (fun (n_u, m_u) ->
          Log.debugf 20 (fun k ->
              k "(@[monoid[%s].on-new-term.sub@ :n %a@ :sub-t %a@ :value %a@])"
                M.name E_node.pp n E_node.pp n_u M.pp m_u);
          let n_u = CC.find cc n_u in
          if CC.get_bitfield cc field_has_value n_u then (
            let m_u' =
              try Cls_tbl.find values n_u
              with Not_found ->
                Error.errorf "node %a has bitfield but no value" E_node.pp n_u
            in

            match M.merge cc plugin_st n_u m_u n_u m_u' (Expl.mk_list []) with
            | Error (CC.Handler_action.Conflict expl) ->
              Error.errorf
                "when merging@ @[for node %a@],@ values %a and %a:@ conflict %a"
                E_node.pp n_u M.pp m_u M.pp m_u' Expl.pp expl
            | Ok (m_u_merged, merge_acts) ->
              acts := List.rev_append merge_acts !acts;
              Log.debugf 20 (fun k ->
                  k
                    "(@[monoid[%s].on-new-term.sub.merged@ :n %a@ :sub-t %a@ \
                     :value %a@])"
                    M.name E_node.pp n E_node.pp n_u M.pp m_u_merged);
              Cls_tbl.add values n_u m_u_merged
          ) else (
            (* just add to [n_u] *)
            CC.set_bitfield cc field_has_value true n_u;
            Cls_tbl.add values n_u m_u
          ))
        l;
      !acts

    let iter_all : _ Iter.t = Cls_tbl.to_iter values

    let on_pre_merge cc n1 n2 e_n1_n2 : CC.Handler_action.or_conflict =
      let exception E of CC.Handler_action.conflict in
      let acts = ref [] in
      try
        (match get n1, get n2 with
        | Some v1, Some v2 ->
          Log.debugf 5 (fun k ->
              k
                "(@[monoid[%s].on_pre_merge@ (@[:n1 %a@ :val1 %a@])@ (@[:n2 \
                 %a@ :val2 %a@])@])"
                M.name E_node.pp n1 M.pp v1 E_node.pp n2 M.pp v2);
          (match M.merge cc plugin_st n1 v1 n2 v2 e_n1_n2 with
          | Ok (v', merge_acts) ->
            acts := merge_acts;
            Cls_tbl.remove values n2;
            (* only keep repr *)
            Cls_tbl.add values n1 v'
          | Error c -> raise (E c))
        | None, Some cr ->
          CC.set_bitfield cc field_has_value true n1;
          Cls_tbl.add values n1 cr;
          Cls_tbl.remove values n2 (* only keep reprs *)
        | Some _, None -> () (* already there on the left *)
        | None, None -> ());
        Ok !acts
      with E c -> Error c

    let pp out () : unit =
      let pp_e out (t, v) =
        Fmt.fprintf out "(@[%a@ :has %a@])" E_node.pp t M.pp v
      in
      Fmt.fprintf out "(@[%a@])" (Fmt.iter pp_e) iter_all

    let () =
      (* hook into the CC's events *)
      Event.on (CC.on_new_term cc) ~f:(fun (_, r, t) -> on_new_term cc r t);
      Event.on (CC.on_pre_merge2 cc) ~f:(fun (_, ra, rb, expl) ->
          on_pre_merge cc ra rb expl);
      ()
  end

  let create_and_setup ?size (cc : CC.t) : t =
    (module Make (struct
      let size = size
      let cc = cc
    end))

  let push_level ((module P) : t) = P.push_level ()
  let pop_levels ((module P) : t) n = P.pop_levels n
  let n_levels ((module P) : t) = P.n_levels ()
  let mem ((module P) : t) t = P.mem t
  let get ((module P) : t) t = P.get t
  let iter_all ((module P) : t) = P.iter_all
  let pp out ((module P) : t) = P.pp out ()
end
