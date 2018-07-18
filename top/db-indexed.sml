structure DBIndexed :> DATABASE =
struct

open Sequent

structure L = Label

structure LM = HashTableFn (struct
                              type hash_key = Label.label
                              val hashVal = Label.hash
                              fun sameKey (x, y) = Label.compare (x, y) = EQUAL
                            end)

structure IM = IntHashTable

structure IS = IntSet

val db : Rule.conc list LM.hash_table = LM.mkTable (1024, Fail "whatever")

open P.Desc

fun register (conc as {prin, ...} : Rule.conc) =
      LM.insert db (prin, (case LM.find db prin of
                             SOME seqs => conc :: seqs
                           | NONE => [conc]))

exception Success

fun fsub (c as {seq as SEQUENT {left = (unr, aff, lin), right = (right, _), ...}, prin}) =
    let
      fun check l =
          let in
            case LM.find db l of
              SOME seqs =>
                List.app (fn {seq = s, ...} => if subsumes (s, seq) then raise Success else ()) seqs
            | NONE => ()
          end

      fun pcheck l = if not (Label.eq (prin, l)) then check l else ()

      fun pc (l, _) = pcheck l

      val res = 
          (check prin;
           Option.map pcheck right;
           Label.Map.appi pc aff;
           Label.Map.appi pc unr;
           Label.Map.appi pc lin;
           false) handle Success => true
    in
      res
    end

fun report () = ()

fun reset () = (LM.clear db)

end
