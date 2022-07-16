(*

and datatype = {
  data_cstors: data_cstor ID.Map.t lazy_t;
}

(* TODO: in cstor, add:
   - for each selector, a special "magic" term for undefined, in
     case the selector is ill-applied (Collapse 2)  *)

(* a constructor *)
and data_cstor = {
  cstor_ty: ty;
  cstor_args: ty array; (* argument types *)
  cstor_proj: cst array lazy_t; (* projectors *)
  cstor_test: cst lazy_t; (* tester *)
  cstor_cst: cst; (* the cstor itself *)
  cstor_card: ty_card; (* cardinality of the constructor('s args) *)
}

val make_cstor : ID.t -> Ty.t -> data_cstor lazy_t -> t
val make_proj : ID.t -> Ty.t -> data_cstor lazy_t -> int -> t
val make_tester : ID.t -> Ty.t -> data_cstor lazy_t -> t
val make_defined : ID.t -> Ty.t -> term lazy_t -> cst_defined_info -> t
val make_undef : ID.t -> Ty.t -> t

let make_cstor id ty cstor =
  let _, ret = Ty.unfold ty in
  assert (Ty.is_data ret);
  make id (Cst_cstor cstor)
let make_proj id ty cstor i =
  make id (Cst_proj (ty, cstor, i))
let make_tester id ty cstor =
  make id (Cst_test (ty, cstor))

val cstor_test : data_cstor -> term -> t
val cstor_proj : data_cstor -> int -> term -> t
val case : term -> term ID.Map.t -> t

let case u m = Case (u,m)
let if_ a b c =
  assert (Ty.equal b.term_ty c.term_ty);
  If (a,b,c)

let cstor_test cstor t =
  app_cst (Lazy.force cstor.cstor_test) (CCArray.singleton t)

let cstor_proj cstor i t =
  let p = CCArray.get (Lazy.force cstor.cstor_proj) i in
  app_cst p (CCArray.singleton t)

   *)
