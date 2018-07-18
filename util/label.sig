signature LABEL =
sig
  type label

  (* distinguished labels *)
  val one : label
  val zero : label
  val top : label

  (* atomic labels *)
  val named : string -> label
  val named' : Atom.atom -> label

  val is_named : label -> bool
  val name : label -> Atom.atom

  val eq : label * label -> bool
  val neq : label * label -> bool

  val compare : label * label -> order
  val hash : label -> word

  val new : unit -> label
  val reset : unit -> unit

  structure Map : MAP where type Key.ord_key = label
  structure Set : SET where type Key.ord_key = label

  type 'a map = 'a Map.map
  type set = Set.set

  (* pretty printing *)
  val pp : label -> P.pp_desc
end
