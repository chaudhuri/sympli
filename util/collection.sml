signature KEY =
sig
  include ORD_KEY

  val pp : ord_key -> P.pp_desc
end


signature MAP =
sig
  include ORD_MAP

  val digest : (Key.ord_key * 'a) list -> 'a map
  val pp : ('a -> P.pp_desc) -> 'a map -> P.pp_desc
end

functor MapFn (K : KEY) :>
        MAP where type Key.ord_key = K.ord_key =
struct

(* structure UnderlyingMap = BinaryMapFn (K)  *)
structure UnderlyingMap = RedBlackMapFn (K)
open UnderlyingMap


fun digest l = List.foldr insert' empty l

open P.Desc
fun pp P s =
      hvBox (P.Rel 0,
             P.delimit [string ",", space 1]
                       (fn (v, t) => hBox [K.pp v, string ":", P t])
                       (listItemsi s))

end

structure IntMap = MapFn (struct
                            open Int
                            type ord_key = int
                            val pp = P.Desc.string o Int.toString
                          end)

structure AtomMap = MapFn (struct
                             open Atom
                             type ord_key = atom
                             val pp = P.Desc.string o Atom.toString
                           end)

signature SET =
sig
  include ORD_SET

  val pp : set -> P.pp_desc
end

functor SetFn (K : KEY) :>
        SET where type Key.ord_key = K.ord_key =
struct

(* structure UnderlyingSet = BinarySetFn (K) *)
structure UnderlyingSet = RedBlackSetFn (K)
open UnderlyingSet

open P.Desc

fun pp S = hBox [string "{",
                 hvBox (P.Rel 0,
                         P.delimit [string ",", space 1] K.pp (listItems S)),
                 string "}"]



end

structure IntSet = SetFn (struct
                            open Int
                            type ord_key = int
                            val pp = P.Desc.string o Int.toString
                          end)
