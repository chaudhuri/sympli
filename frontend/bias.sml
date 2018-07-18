(* 
 * biases.sml --- biases
 * 
 * Copyright (C) 2005  Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * 
 * This file is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *)

signature BIAS =
sig

datatype bias = Left | Right
val default : bias ref

val reset : unit -> unit

val setbias : Atom.atom * bias -> unit

val biasof : Atom.atom -> bias

end

structure Bias :> BIAS =
struct

datatype bias = Left | Right

structure AM = AtomMap
               
val biases : bias AM.map ref = ref AM.empty
val default : bias ref = ref Right

fun setbias (x, b) = biases := AM.insert (!biases, x, b)

fun reset () = biases := AM.empty

fun biasof x =
    (case AM.find (!biases, x) of
       SOME b => b
     | NONE => !default)

end
