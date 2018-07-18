(* 
 * Focusing rules
 * Author: Kaustuv Chaudhuri
 *)

signature RULE2 =
sig

exception Partial

(* conclusion of rules *)
type conc = {seq : Sequent.sequent, prin : Label.label}


(* derived rules *)
datatype rule = Fin of Sequent.sequent -> conc
              | Par of Sequent.sequent -> rule

val apply : rule -> Sequent.sequent -> rule option
val isfin : rule -> bool

(* initial sequent for the given literal *)
val init : Lit2.lit -> conc

(*
 * specialize rules for a given literal based on its skeleton
 *)
val spec : Lit2.lit -> conc list * rule list

end
