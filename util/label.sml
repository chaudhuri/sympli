structure Label :> LABEL =
struct

infixr 0 $
fun f $ x = f x

datatype label = IL of int
               | SL of Atom.atom

fun named s = SL (Atom.atom s)
val named' = SL

val one = named "1"
val zero = named "0"
val top = named "#"

fun eq (IL x, IL y) = x = y
  | eq (SL A, SL B) = Atom.sameAtom (A, B)
  | eq _ =  false

fun neq (l1, l2) = not $ eq (l1, l2)

fun is_named (SL _) = true
  | is_named _ = false

fun name (SL name) = name

fun compare (IL x, IL y) = Int.compare (x, y)
  | compare (SL A, SL B) = Atom.compare (A, B)
  | compare (IL _, SL _) = LESS
  | compare (SL _, IL _) = GREATER

fun hash (IL x) = IntHashTable.Key.hashVal x
  | hash (SL x) = Atom.hash x

val store = ref 0
fun reset_store () = store := 0

fun new () = IL (!store) before store := !store + 1

local open P.Desc in
fun pp (IL l) = string ("L" ^ Int.toString l)
  | pp (SL A) = string (Atom.toString A)
end


structure LK : KEY =
  struct
  
  type ord_key = label
  val compare = compare

  val pp = pp

  end

structure Map = MapFn (LK)
structure Set = SetFn (LK)

type 'a map = 'a Map.map
type set = Set.set

(* resets *)
fun reset () = reset_store ()

end
