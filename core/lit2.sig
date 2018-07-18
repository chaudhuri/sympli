(* 
 * Two-phase labelling
 * Author: Kaustuv Chaudhuri
 *)

signature LIT2 =
sig

  include LIT

  (* passive phase *)
  val lpass : Prop.prop -> lit
  val rpass : Prop.prop -> lit

  (* active phase *)
  val lact : Prop.prop -> lit
  val ract : Prop.prop -> lit

end
