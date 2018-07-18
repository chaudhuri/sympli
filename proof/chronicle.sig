(* 
 * Proof chronicles
 * Author: Kaustuv Chaudhuri
 *)

signature CHRONICLE =
sig

  type label = Label.label

  (* 
   * A chronicle is a proof stripped of all detail; the only things noted
   * are the literals that participated in various rules. A final proof
   * (see proof.sig) should be recoverable from a chronicle -- and partial
   * proofs from partial chronicle -- given the end sequent of the
   * chronicle.
   * 
   * To make the recoverty deterministic, binary multiplicative keep track
   * of the *left* half of the split context.
   *)
  datatype chronicle = 
           Init of label

         | Copy of label * chronicle

         | TensR of label list * chronicle * chronicle
         | TensL of label * chronicle

         | OneR
         | OneL of label * chronicle

         | LimpR of chronicle
         | LimpL of label list * label * chronicle * chronicle

         | WithR of chronicle * chronicle
         | WithL1 of label * chronicle
         | WithL2 of label * chronicle

         | TopR

         | ChoiceR1 of chronicle
         | ChoiceR2 of chronicle
         | ChoiceL of label * chronicle * chronicle

         | ZeroL of label

         | BangR of chronicle
         | BangL of label * chronicle

         | BraceR of chronicle
         | BraceL of label * chronicle


  (* pretty printing *)

  val pp : chronicle -> P.pp_desc

end
