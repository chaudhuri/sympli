signature ONF =
sig

val onf : Prop.prop -> Prop.prop * (Proof.chk -> Proof.chk)

end
