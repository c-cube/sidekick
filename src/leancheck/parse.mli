module type CALLBACK = Parse_intf.CALLBACK

type callback = (module CALLBACK)
type input = [ `String of string | `In of in_channel ]

val parse : ?max_errors:int -> input -> callback -> unit
