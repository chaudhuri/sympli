(* 
 * Proof normalization
 * Created: Sun Jun  6 05:34:37 EDT 2004
 *)


(* A choice of *two* delicacies *)

(* norm-fp.sml *)
(* structure Norm = DirectNorm *)

(* norm-kc.fun *)
structure Norm = FoldNormFn (structure Fold = Fold.Always)
