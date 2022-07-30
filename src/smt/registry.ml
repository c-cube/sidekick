
  (* registry keys *)
  module type KEY = sig
    type elt

    val id : int

    exception E of elt
  end

  type 'a key = (module KEY with type elt = 'a)
  type t = { tbl: exn Util.Int_tbl.t } [@@unboxed]

  let create () : t = { tbl = Util.Int_tbl.create 8 }
  let n_ = ref 0

  let create_key (type a) () : a key =
    let id = !n_ in
    incr n_;
    let module K = struct
      type elt = a

      exception E of a

      let id = id
    end in
    (module K)

  let get (type a) (self : t) (k : a key) : _ option =
    let (module K : KEY with type elt = a) = k in
    match Util.Int_tbl.get self.tbl K.id with
    | Some (K.E x) -> Some x
    | _ -> None

  let set (type a) (self : t) (k : a key) (v : a) : unit =
    let (module K) = k in
    Util.Int_tbl.replace self.tbl K.id (K.E v)
