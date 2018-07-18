signature DATABASE =
sig

val reset : unit -> unit

val register : Rule.conc -> unit

val fsub : Rule.conc -> bool

val report : unit -> unit

end
