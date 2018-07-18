signature FLAG =
  sig
    type flag

    val flag : string -> flag
    val not : flag -> flag

    val set : flag -> unit
    val unset : flag -> unit
    val isset : flag -> bool

    val guard : flag -> ('a -> unit) -> 'a -> unit
    val guards : flag list -> ('a -> unit) -> 'a -> unit
    val someguards : flag list -> ('a -> unit) -> 'a -> unit

    val branch : flag -> ('a -> 'b) * ('a -> 'b) -> 'a -> 'b

    val show : flag -> string
  end

structure Flag :> FLAG =
  struct
    datatype flag = FLAG of {name : string, value : bool ref, post : bool -> bool}
      
    fun flag name = FLAG {name = name, value = ref false, post = fn b => b}
      
    fun set (FLAG f) = #value f := true
    fun unset (FLAG f) = #value f := false
    fun not (FLAG {name, value, post}) =
          FLAG {name = name, value = value, post = fn b => Bool.not (post b)}
      
    fun isset (FLAG f) = (#post f) (! (#value f))
      
    fun guard fl f x = if isset fl then f x else ()
    fun guards fls f x = if List.all isset fls then f x else ()
    fun someguards fls f x = if List.exists isset fls then f x else ()

    fun branch fl (f, g) = if isset fl then f else g
      
    fun show (FLAG f) = "flag " ^ #name f ^ " = " ^ Bool.toString (! (#value f))
  end
