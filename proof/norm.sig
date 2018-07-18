(* Proof normalization *)

signature NORM =
sig
  (* cnorm(c) = n, the normal form of c, c closed *)
  val cnorm : Proof.chk -> Proof.chk
end

