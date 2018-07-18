(* 
 * Focusing rules
 * Author: Kaustuv Chaudhuri
 *)

structure Rule2 (* :> RULE2 *) =
struct

open Lit2
structure C = Chronicle

structure L = Label
structure LM = L.Map

exception Partial

(* conclusion of rules *)
type conc = {seq : Sequent.sequent, prin : Label.label}

(* derived rules *)
datatype rule = Fin of Sequent.sequent -> conc
              | Par of Sequent.sequent -> rule

fun apply (Fin f) s = NONE
  | apply (Par f) s = SOME (f s)

fun isfin (Fin f) = true
  | isfin _ = false

val ` = Sequent.SEQUENT

(* initial sequents *)

fun init (plit as Named (l, s, k))=
      {seq = `{left = (LM.empty, LM.empty, LM.digest [(l, 1)]),
               right = SOME l,
               weak = false,
               chron = C.Init l},
       prin = l}





(*
 * specialize rules for a given literal based on its skeleton
 *)
fun spec _ = raise Fail "foo"

end
