(* rules *)

signature RULE =
sig

(* conclusion of rules *)
type conc = {seq : Sequent.sequent, prin : Label.label}
val pp_conc : conc -> P.pp_desc

(* derived rules *)
datatype rule = Par of Sequent.sequent -> rule
              | Conc of conc

val apply : rule -> Sequent.sequent -> rule option
val is_conc : rule -> bool
val is_par : rule -> bool

end
