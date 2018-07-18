(* Timers collecting statistics about Twelf *)
(* Author: Frank Pfenning *)

functor TimersFn (structure Timing : TIMING)
        :> TIMERS where type Timing.center = Timing.center =
struct

  structure Timing = Timing

  val parsing    = Timing.newCenter ("Parsing       ")
  val search     = Timing.newCenter ("Search        ")
  val fsub       = Timing.newCenter ("Forw. Subs.   ")
  val validation = Timing.newCenter ("Validation    ")

  val centers = [parsing, search, fsub, validation]
  val tots = [parsing, search, validation]

  val total      = Timing.sumCenter ("Total         ", tots)

  val time = Timing.time
  fun time1 c f x1 = time c f x1
  fun time2 c f x1 x2 = time c (f x1) x2
  fun time3 c f x1 x2 x3 = time c (f x1 x2) x3
  fun time4 c f x1 x2 x3 x4 = time c (f x1 x2 x3) x4

  fun reset () = List.app Timing.reset centers

  open P.Desc
  fun check () =
        Comm.send
          "timers"
          (fn () => vBox (P.Rel 0,
                          P.delimit [cut] (string o Timing.toString) centers
                          @ [cut, string (Timing.sumToString total)]))

  fun show () = (check (); reset ()) 

end;  (* functor Timers *)
