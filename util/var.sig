signature VAR =
sig

type center
val center : {prefix : string, name : string} -> center
val global : center

val reset : unit -> unit
val reset' : center -> unit

val resetTo : int -> unit
val resetTo' : center -> int -> unit

type var
val named : string -> var
val named' : center -> string -> var

val eq : var * var -> bool
val compare : var * var -> order

val fresh : string -> var
val fresh' : center -> string -> var

structure Set : SET where type Key.ord_key = var
structure Map : MAP where type Key.ord_key = var

type set = Set.set
type 'a map = 'a Map.map

val pp : var -> P.pp_desc
end

