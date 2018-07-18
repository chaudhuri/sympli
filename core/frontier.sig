(* 
 * Frontiers
 * Author: Kaustuv Chaudhuri
 *)

(*
 * Frontier nodes in a subformula tree corresponding to any given formula
 * are those nodes that are
 * 
 *   1. Left- or right-synchronous, as appropriate; and
 *   2. Not an operand of a left- or right- synchronous connective
 * 
 * In addition, the root node is itself a frontier node.
 * 
 * 
 * For instance, the frontier nodes of
 * 
 *     A * B & A * C -o A * (B + C)
 *     `---'   `---'         `---'
 *      L2      L3            L5
 *       `------'       `-----'
 *         L1             L4
 *          `-------------'
 *                L0
 *     
 * are:
 * 
 *    L0 = A * B & A * C -o A * (B + C)
 *    l1 = A * B & A * C
 *    L4 = A * (B + C)
 *)

signature FRONTIER = 
sig

  (* 
   * A maul is a particular path in a focusing phase. Fronts are
   * transition points, Joins are conjunctive nodes, and Lefts and Rights
   * are disjunctive nodes. and Lax strips a {}
   *
   * To illustrate, the mauls corresponding to L1 in the above example are:
   * 
   *      Left (Front)
   *      Right (Front)
   *
   * Similarly, those of L4 are:
   * 
   *      Join (Front, Left (Front))
   *      Join (Front, Right (Front))
   *)
  datatype maul = Front
                | Join of maul * maul
                | Left of maul
                | Right of maul
                | Lax of maul

  (* 
   * find all frontier nodes in the given literal, together with all the
   * associated mauls
   *)
  val frontier : Lit.lit -> (Lit.lit * maul) list


  (* pretty printing *)
  val pp_maul : maul -> P.pp_desc
end



