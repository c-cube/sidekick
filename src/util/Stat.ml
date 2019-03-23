
(** {1 Statistics} *)

module Fmt = CCFormat
module S_map = CCMap.Make(String)

type 'a counter = {
  name: string;
  mutable count: 'a;
}

type ex_counter =
  | C_int : int counter -> ex_counter
  | C_float : float counter -> ex_counter

type t = {
  mutable cs: ex_counter S_map.t;
}

let create() : t = {cs=S_map.empty}
let register_ self name c = self.cs <- S_map.add name c self.cs
let all (self:t) = S_map.values self.cs

let mk_int self name =
  match S_map.find name self.cs with
  | C_int s -> s
  | _ -> Error.errorf "incompatible types for stat %S" name
  | exception Not_found ->
    let c = {name; count=0} in
    register_ self name (C_int c); c

let mk_float self name =
  match S_map.find name self.cs with
  | C_float s -> s
  | _ -> Error.errorf "incompatible types for stat %S" name
  | exception Not_found ->
    let c = {name; count=0.} in
    register_ self name (C_float c); c

let[@inline] incr x = x.count <- 1 + x.count
let[@inline] incr_f x by = x.count <- by +. x.count

let pp_all out l =
  let pp_w out = function
    | C_int {name; count} -> Fmt.fprintf out "@[:%s %d@]" name count
    | C_float {name; count} -> Fmt.fprintf out "@[:%s %.4f@]" name count
  in
  Fmt.fprintf out "(@[stats@ %a@])" Fmt.(seq ~sep:(return "@ ") pp_w) l

let global = create()
