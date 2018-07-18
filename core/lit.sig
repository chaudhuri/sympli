(* 
 * Literals
 * Author: Kaustuv Chaudhuri
 *)

(* Note: ALL subformulas are labelled, not just the frontier. *)

signature LIT =
sig

  datatype sign = Pos | Neg

  val flip : sign -> sign

  datatype mode = NORMAL                (* linear        *)
                | HEAVY                 (* operand of !  *)
                | AFFINE                (* operand of &1 *)

  datatype lit = LIT of {label : Label.label,  (* name of literal *)
                         skel : lit Prop.skel, (* skeleton *)
                         sign : sign,
                         unr : bool ref,       (* descendant of ! *)
                         mode : mode ref}

  type skel = lit Prop.skel

  val eq_lit : lit * lit -> bool
  val eq_skel : skel * skel -> bool

  (* trivial labelling *)
  val triv : Prop.prop -> lit
  val triv' : Prop.prop -> skel

  (* labelling *)
  val label : Prop.prop * sign -> lit

  (* register *)
  structure Register :
            sig 
              val reset : unit -> unit
              val lookup : Label.label -> lit option
              val skels : unit -> lit list
            end

  (* pretty printing *)
  val pp : int -> lit -> P.pp_desc
  val itemize_lit : int -> lit -> P.item
  val pp_skel : int -> skel -> P.pp_desc

end
