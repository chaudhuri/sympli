(* basic propositions *)

structure Prop :> PROP =
struct

infixr 0 %
fun f % x = f x

(* propositional skeletons *)
datatype 'prop skel = Atomic of Atom.atom
                    | Tensor of 'prop * 'prop | One
                    | Limp of 'prop * 'prop
                    | With of 'prop * 'prop   | Top
                    | Choice of 'prop * 'prop | Zero
                    | Bang of 'prop
                    | Brace of 'prop

(* propositions with trivial skeletons *)
datatype prop = Prop of pskel
withtype pskel = prop skel


fun eq_skel EQ (Atomic P, Atomic Q) =
      Atom.sameAtom (P, Q)
  | eq_skel EQ (Tensor (A, B), Tensor (A', B')) = 
      EQ (A, A') andalso EQ (B, B')
  | eq_skel EQ (One, One) = true
  | eq_skel EQ (Limp (A, B), Limp (A', B')) = 
      EQ (A, A') andalso EQ (B, B')
  | eq_skel EQ (With (A, B), With (A', B')) = 
      EQ (A, A') andalso EQ (B, B')
  | eq_skel EQ (Top, Top) = true
  | eq_skel EQ (Choice (A, B), Choice (A', B')) = 
      EQ (A, A') andalso EQ (B, B')
  | eq_skel EQ (Zero, Zero) = true
  | eq_skel EQ (Bang A, Bang B) = EQ (A, B)
  | eq_skel EQ _ = false

fun eq_prop (Prop p1, Prop p2) = eq_skel eq_prop (p1, p2)



(* pretty printing *)

open P.Desc
     
datatype item = datatype P.item
datatype opr = datatype P.opr
datatype assoc = datatype P.assoc

fun itemize_skel ITEM =
    let
      fun for (Atomic P) = Atm % string % Atom.toString P
        | for (Limp (A, B)) = 
            Opr (Infix (1, Right, ITEM A, ITEM B), string "-o")
        | for (Choice (A, B)) = 
            Opr (Infix (2, Left, ITEM A, ITEM B), string "+")
        | for (With (A, B)) = 
            Opr (Infix (3, Left, ITEM A, ITEM B), string "&")
        | for (Tensor (A, B)) = 
            Opr (Infix (4, Left, ITEM A, ITEM B), string "*")
        | for (Bang A) = 
            Opr (Prefix (5, ITEM A), string "!")
        | for (Brace A) = 
            Bra (string "{", ITEM A, string "}")
        | for One = Atm % string "1"
        | for Zero = Atm % string "0"
        | for Top = Atm % string "#"
    in
      for
    end

fun itemize (Prop P) = itemize_skel itemize P

val pp_prop = P.lineate o itemize

fun pp_skel ITEM = P.lineate o itemize_skel ITEM

end
