signature ENGINE =
sig
  exception Invalid
  exception Saturated
  val prove : Prop.prop * bool * int -> Proof.chk option
end
