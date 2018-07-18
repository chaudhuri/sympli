structure Var :> VAR =
struct

datatype center = CENTER of {prefix : string,
                             name : Atom.atom option,
                             store : int ref}

val global = CENTER {prefix = "v", name = NONE, store = ref 1}
fun center {prefix, name} = CENTER {prefix = prefix, name = SOME (Atom.atom name), store = ref 1}

fun resetTo' (CENTER c) n = #store c := n
fun resetTo n = resetTo' global n

fun reset' c = resetTo' c 1
fun reset () = reset' global

datatype var = IV of int * center
             | SV of Atom.atom * center

fun named' c s = SV (Atom.atom s, c)
fun named s = named' global s

fun fresh' (c as CENTER {store, ...}) s = IV (!store, c) before store := !store + 1
fun fresh s = fresh' global s

fun name (CENTER {name, ...}) = name

fun name_eq (c1, c2) =
    (case (name c1, name c2) of
       (SOME n1, SOME n2) => Atom.sameAtom (n1, n2)
     | (NONE, NONE) => true
     | _ => false)

fun name_compare (c1, c2) k =
    (case (name c1, name c2) of
       (SOME n1, SOME n2) =>
          let val com = Atom.compare (n1, n2)
          in if com = EQUAL then k () else com end
     | (NONE, NONE) => k ()
     | (NONE, SOME _) => LESS
     | (SOME _, NONE) => GREATER)

fun eq (IV (x, cx), IV (y, cy)) =
      name_eq (cx, cy) andalso x = y
  | eq (SV (A, cA), SV (B, cB)) =
      name_eq (cA, cB) andalso Atom.sameAtom (A, B)
  | eq _ =  false

fun compare (IV (x, cx), IV (y, cy)) = 
      name_compare (cx, cy) (fn () => Int.compare (x, y))
  | compare (SV (A, cA), SV (B, cB)) = 
      name_compare (cA, cB) (fn () => Atom.compare (A, B))
  | compare (IV _, SV _) = LESS
  | compare (SV _, IV _) = GREATER

local open P.Desc in
fun pp (IV (l, CENTER {prefix, ...})) =
      string (prefix ^ Int.toString l)
  | pp (SV (A, _)) = string (Atom.toString A)
end

structure VarKey : KEY =
  struct
    type ord_key = var
    val compare = compare
    val pp = pp
  end 

structure Set = SetFn (VarKey)
structure Map = MapFn (VarKey)

type set = Set.set
type 'a map = 'a Map.map


end
