(* 
 * Rules
 * Author: Kaustuv Chaudhuri
 *)

functor RuleFn (structure Lit : LIT) :>
        RULE where type Lit.lit = Lit.lit =
struct

structure Lit = Lit

structure Seq = Sequent
datatype sequent = datatype Seq.sequent

type label = Label.label

(* conclusion of fully instantiated rules *)
type conc = {seq : sequent, prin : label}

datatype rule = Par of sequent -> rule
              | Conc of conc

fun apply (Conc c) s = NONE
  | apply (Par f) s = SOME (f s)

fun is_conc (Conc _) = true
  | is_conc _ = false

fun is_par (Par _) = true
  | is_par _ = false

end
