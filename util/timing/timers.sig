(* Original author: Frank Pfenning *)

signature TIMERS =
sig

  structure Timing : TIMING

  (* Programming interface *)
  val parsing    : Timing.center
  val search     : Timing.center
  val fsub       : Timing.center
  val validation : Timing.center

  (* Warning: time for printing of the answer substitution to a
     query is counted twice here.
  *)
  val total : Timing.sum		(* total time *)

  (* timen center f x1 ... xn = y
     if f x1 ... xn = y and time of computing f x1 ... xn is added to center.
     If f x1 ... xn raises an exception, it is re-raised.
  *)
  val time1 : Timing.center -> ('a -> 'b) -> 'a -> 'b
  val time2 : Timing.center -> ('a -> 'b -> 'c) -> 'a -> 'b -> 'c
  val time3 : Timing.center -> ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
  val time4 : Timing.center -> ('a -> 'b -> 'c -> 'd -> 'e) -> 'a -> 'b -> 'c -> 'd -> 'e

  (* External interface *)
  val reset : unit -> unit		(* reset above centers *)

  val check : unit -> unit		(* check timer values *)
  val show  : unit -> unit		(* check, then reset *)

end;  (* signature TIMERS *)
