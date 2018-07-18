(* Timers *)
(* Author: Frank Pfenning *)

structure Timers =
  TimersFn (structure Timing = Timing);

(* alternative not using actual timers *)
(*
structure Timers =
  Timers (structure Timing' = Counting);
*)
