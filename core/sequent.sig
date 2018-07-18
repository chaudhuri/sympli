(* 
 * Sequents
 * Author: Kaustuv Chaudhuri
 *)

signature SEQUENT =
sig
  type ctx = int Label.map              (* nuumber of occurrences *)
  type right = Label.label option * bool
  type left = ctx * ctx * ctx

  type sequent' = {left : left, right : right, weak : bool}
  datatype sequent = SEQUENT of {left : left,
                                 right : right,
                                 weak : bool,
                                 chron : Chronicle.chronicle}

  (* equality *)
  val eq_ctx : ctx * ctx -> bool
  val eq_right : right * right -> bool
  val eq_sequent : sequent * sequent -> bool

  (* rename variables and renumber hypotheses *)
  val rename : sequent -> sequent

  exception Partial

  (* eagerly factor *)
  val factor : sequent -> sequent

  (* extraction *)
  datatype emode = STRICT | NORMAL | LAX
  val remove : emode -> left * Lit.lit
               -> {left : left, fresh : bool,
                   refl : Chronicle.chronicle -> Chronicle.chronicle} option

  (* multiplicative join *)
  val join : left * left -> left
  val join' : left * Label.label -> left

  (* additive join *)
  val add : (left * bool) * (left * bool) -> left

  (* subsumption *)
  val subsumes : sequent * sequent -> bool
  val subsumes' : sequent -> sequent' -> bool

  (* validation *)
  val proof : sequent -> Proof.ctx * Proof.chk * Lit.skel option * bool
  val valid : sequent -> bool

  (* pretty printing *)
  val pp_ctx : ctx -> P.pp_desc
  val pp_right : right -> P.pp_desc
  val pp_sequent : sequent -> P.pp_desc
  val pp_sequent' : {left : left, right : right, weak : bool} -> P.pp_desc

end
