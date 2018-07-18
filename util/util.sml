structure Util =
struct
fun fst (a, b) = a
fun snd (a, b) = b

type 'a eq = 'a * 'a -> bool
type 'a compare = 'a * 'a -> order
type 'a pp = 'a -> P.pp_desc
type 'a item = 'a -> P.item

end

structure U = Util
