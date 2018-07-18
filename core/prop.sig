(* basic propositions *)

signature PROP =
sig

  (* propositional skeletons *)
  datatype 'prop skel = Atomic of Atom.atom
                      | Tensor of 'prop * 'prop | One
                      | Limp of 'prop * 'prop
                      | With of 'prop * 'prop   | Top
                      | Choice of 'prop * 'prop | Zero
                      | Bang of 'prop
                      | Brace of 'prop

  (* propositions with trivial skeletons *)
  datatype prop = Prop of prop skel
  type pskel = prop skel

  val eq_skel : ('prop * 'prop -> bool)
                -> 'prop skel * 'prop skel -> bool

  val eq_prop : prop * prop -> bool

  (* pretty printing *)

  val itemize_skel : ('prop -> P.item) -> 'prop skel -> P.item
  val itemize : prop -> P.item

  val pp_prop : prop -> P.pp_desc
  val pp_skel : ('prop -> P.item) -> 'prop skel -> P.pp_desc

end
