(* 
 * Rule generation
 * Author: Kaustuv Chaudhuri
 *)

signature RULE_GEN =
sig

val spec : Lit.lit -> Rule.rule list

end
