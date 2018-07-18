(* 
 * Rules
 * Author: Kaustuv Chaudhuri
 *)

structure Rule :> RULE =
struct

structure Lit = Lit

structure Seq = Sequent
datatype sequent = datatype Seq.sequent

type label = Label.label

(* conclusion of fully instantiated rules *)
type conc = {seq : sequent, prin : label}

datatype rule = Par of sequent -> rule
              | Conc of conc

exception Partial

fun apply (Conc c) s = NONE
  | apply (Par f) s = SOME (f s)

fun is_conc (Conc _) = true
  | is_conc _ = false

fun is_par (Par _) = true
  | is_par _ = false

open P.Desc
fun pp_conc {seq, prin} = hBox [Seq.pp_sequent seq, string " | ", Label.pp prin]

end
