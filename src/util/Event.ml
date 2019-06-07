
type 'a small_set =
  | S0
  | S1 of 'a
  | S2 of 'a * 'a
  | S3 of 'a * 'a * 'a * 'a small_set

type 'a t = {
  mutable set: ('a -> unit) small_set;
}

let[@unroll 1] rec cons_ f set = match set with
  | S0 -> S1 f
  | S1 f2 -> S2(f,f2)
  | S2(f2,f3) -> S3 (f,f2,f3, S0)
  | S3(f1,f2,f3,tl) -> S3 (f,f1,f2,cons_ f3 tl)

let on (e:_ t) f : unit =
  let set' = cons_ f e.set in
  e.set <- set'

module Emitter = struct
  type nonrec 'a t = 'a t

  let rec fire_set_ set x =
    match set with
    | S0 -> ()
    | S1 f -> f x
    | S2 (f1,f2) -> f1 x; f2 x
    | S3 (f1,f2,f3,tl) -> f1 x; f2 x; f3 x; fire_set_ tl x

  let[@inline] fire e x = fire_set_ e.set x
end

let make () =
  let e = {set=S0} in
  e, e

