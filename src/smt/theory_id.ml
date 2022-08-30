include CCInt

type state = int ref

let create () = ref 1

let fresh (self : state) =
  let n = !self in
  incr self;
  n

module Set = Util.Int_set
