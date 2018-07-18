structure DBTriv :> DATABASE =
struct

open Sequent

structure L = Label
structure LM = Label.Map

val db : sequent list ref = ref []

open P.Desc

fun register ({seq, ...} : Rule.conc) =
      (Comm.send "database" (fn () => hBox [string "registered: ", pp_sequent seq]);
       db := seq :: (!db))

fun fsub ({seq, ...} : Rule.conc) =
      List.exists (fn ks => subsumes (ks, seq)) (!db)

fun reset () = (db := [])

fun report () = ()

end
