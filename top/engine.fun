functor EngineFn (structure DB : DATABASE
                  structure Gen : RULE_GEN)
        :> ENGINE =
struct

open P.Desc ExtSyn

structure L = Label
structure LM = L.Map

datatype lit = datatype Lit.lit

exception Saturated
exception Invalid

val send = Comm.send

fun apply (emit, tab) rule {seq, rules} =
    (case Rule.apply rule seq of
       SOME (Rule.Conc c) => NONE before emit c
     | SOME rule => 
         let
           val id = Rules.add tab rule
         in
           rules := id :: (!rules);
           SOME rule
         end
     | NONE => NONE) handle Partial => NONE

fun percolate (emit, tab) active rule =
    let
      val newrules = List.mapPartial (apply (emit, tab) rule) active
    in
      List.app (percolate (emit, tab) active) newrules
    end


fun activate (tab, active) sel =
    let
      val concs = ref []
      fun emit x = concs := x :: (!concs)

      val rules = Rules.rules tab
      val _ = send "loop" (fn () => hBox [string "(* trying ", 
                                          string (Int.toString (List.length rules)),
                                          string " rules *)"])
      val newrules = List.mapPartial (fn rule => apply (emit, tab) rule sel) rules
      val _ = send "loop" (fn () => hBox [string "(* need to percolate ", 
                                          string (Int.toString (List.length newrules)),
                                          string " rules *)"])
    in
      List.app (percolate (emit, tab) active) newrules;
      !concs
    end

datatype counters = COUNTERS of {gen : int ref,
                                 fsubs : int ref,
                                 bsubs : int ref,
                                 iters : int ref}
                                
fun counters () = COUNTERS {gen = ref 0,
                            fsubs = ref 0,
                            bsubs = ref 0,
                            iters = ref 0}
           
fun pp_ctrs (COUNTERS ctrs) = 
    send "counters"
         (fn () =>
             vBox (P.Rel 0, [string "facts generated: ", string (Int.toString (! (#gen ctrs))), cut,
                             string "facts subsumed (forward): ", string (Int.toString (! (#fsubs ctrs))), cut,
                             string "facts subsumed (backward): ", string (Int.toString (! (#bsubs ctrs))), cut,
                             string "#iterations: ", string (Int.toString (! (#iters ctrs)))]))

fun forw (conc as {seq, ...} : Rule.conc, nseqs) =
    if Timers.time1 Timers.fsub DB.fsub conc then nseqs
    else seq :: nseqs before DB.register conc

fun apply rule active = raise Fail "foo"


datatype ostate = OSTATE of {refute : bool,
                             maxiter : int,
                             table : Rules.table,
                             sos : Sequent.sequent list,
                             active : {seq : Sequent.sequent, rules : Rules.rid list ref} list,
                             goal : Sequent.sequent',
                             ctrs : counters}

fun otter (OSTATE {refute, maxiter, table, sos, active, goal, ctrs as COUNTERS {iters, fsubs, bsubs, gen}}) =
    let
      fun doit [] =
          let in
            send "loop" (fn () => hBox [space 6, string "(* SATURATED *)"]);
            if not refute then raise Saturated else NONE
          end
        | doit sos =
          if refute andalso !iters > maxiter
          then (send "loop" (fn () => hBox [space 6, string "(* SATURATED *)"]); NONE)
          else
            let
              val _ = iters := !iters + 1

              val _ = if !iters mod 100 = 0 then pp_ctrs ctrs else ()

              val ind = space 8

              val _ = send "loop" (fn () => hBox [space 6, string "(* OTTER loop starts *)"])

              val _ = send "sos"
                           (fn () => hBox [ind, string "(* sos *)", newline,
                                           space 10, vBox (P.Rel 0, P.delimit [cut] Sequent.pp_sequent sos)])

              val _ = send "active"
                           (fn () => hBox [ind, string "(* active *)", newline,
                                           space 10, vBox (P.Rel 0, P.delimit [cut] (fn {seq, ...} => Sequent.pp_sequent seq) active)])

              val sel = Sequent.rename (List.hd sos)
              val sos = List.tl sos

              val _ = send "sel" 
                           (fn () => hBox [ind, string "(* selected *)", newline,
                                           space 10, Sequent.pp_sequent sel])

              val sel = {seq = Sequent.rename sel, rules = ref []}
              val active = sel :: active
              val nseqs = activate (table, active) sel

              fun pp_conc ({seq, ...} : Rule.conc) = Sequent.pp_sequent seq

              val _ = if List.length nseqs > 0
                      then send "prefactor"
                                (fn () => hBox [ind, string "(* new facts (pre-factoring) *)", newline,
                                                space 10, vBox (P.Rel 0, P.delimit [cut] pp_conc nseqs)])
                      else ()

              fun factor_conc (conc : Rule.conc) : Rule.conc =
                    {seq = Sequent.factor (#seq conc), prin = #prin conc}

              val nseqs = List.map factor_conc nseqs

              val _ = if List.length nseqs > 0 
                      then send "postfactor" 
                                (fn () => hBox [ind, string "(* new facts (after factoring) *)", newline,
                                                space 10, vBox (P.Rel 0, P.delimit [cut] pp_conc nseqs)])
                      else ()

              val ngen = List.length nseqs
              val _ = gen := !gen + ngen

              val nseqs = List.foldr forw [] nseqs

              val _ = fsubs := !fsubs + (ngen - List.length nseqs)

              val _ = if List.length nseqs > 0 
                      then send "fsubs"
                                (fn () => hBox [ind, string "(* new facts (after forward subsumption) *)", newline,
                                                space 10, vBox (P.Rel 0, P.delimit [cut] Sequent.pp_sequent nseqs)])
                      else ()

              val (killed, active) = 
                  List.partition (fn {seq = a, ...} => List.exists (fn ns => Sequent.subsumes (ns, a)) nseqs) active

              val _ = List.app (fn {seq, rules} => List.app Rules.del (!rules)) killed

              val _ = if List.length killed > 0 then
                        (send "bsubs"
                              (fn () => hBox [ind, string "(* backwards subsumption killed ",
                                              string (Int.toString (List.length killed)),
                                              string " sequents! *)"]);
                              bsubs := !bsubs + (List.length killed))
                      else ()
            in
              send "loop" (fn () => hBox [space 6, string "(* OTTER loop ends *)", newline]);
              case List.find (fn ns => Sequent.subsumes' ns goal) nseqs  of
                SOME ns => (send "setup" (fn () => hBox [space 6, string "(* GOAL subsumed *)", newline]);
                            if refute then raise Fail "failed to refute!" else ();
                            (SOME ns))
              | _ => (send "loop" (fn () => hBox [ind, string "(* goal nowhere to be seen *)", newline]);
                      otter (OSTATE {refute = refute,
                                     maxiter = maxiter,
                                     table = table,
                                     sos = sos @ nseqs,
                                     active = active,
                                     goal = goal,
                                     ctrs = ctrs}))
            end
    in
      doit sos
    end

val otter = Timers.time1 Timers.search otter


fun prove (A, refute, iters) =
    let
      val _ = DB.reset ()

      val Ap = Prop.pp_prop A
      val (A1, restore) = Onf.onf A

      val _ = Lit.Register.reset ()

      val goal as LIT glit = Lit.label (A1, Lit.Pos)

      val _ = send "setup"
                   (fn () => vBox (P.Rel 0,
                                   [string "  (* 1. one normal form *)", cut,
                                    string "    ", Prop.pp_prop A1, cut, cut,
                                    string "  (* 2. literals *)", cut,
                                    string "    (* goal *)", cut,
                                    string "      ", Lit.pp 2 goal, cut, cut,
                                    string "    (* literals *)", cut,
                                    string "      ", vBox (P.Rel 0, P.delimit [cut] (Lit.pp 2) (Lit.Register.skels ())), cut]))


      val _ = send "setup" (fn () => string "  (* 3. specializing *)")

      val gseq =  {left = (L.Map.empty, L.Map.empty, L.Map.empty),
                   right = (SOME (#label glit), false),
                   weak = false}

      val front = Frontier.frontier goal

      val _ = send "rules"
                   (fn () =>
                       hBox [string "frontier: ",
                             vBox (P.Rel 0,
                                   P.delimit
                                     [cut]
                                     (fn (l, m) =>
                                         hBox [Lit.pp 10 l,
                                               string " :: ", Frontier.pp_maul m])
                                     front)])

      (* val _ = raise Fail "done" *)

      val (axioms, rules) = List.partition Rule.is_conc (Gen.spec goal)
      val axioms = List.map (fn Rule.Conc c => c) axioms
      val axioms = List.foldr forw [] axioms

      val _ = send "setup"
                   (fn () => hBox [space 7, string "(* axioms *)", newline,
                                   space 5, vBox (P.Rel 0, P.delimit [cut] Sequent.pp_sequent axioms), newline])

      val _ = send "rules"
                   (fn () => hBox [string "    (* #rules: ",
                                   string (Int.toString (List.length rules)),
                                   string " *)"])

      val _ = send "setup"
                   (fn () => hBox [string "  (* 4.b. goal sequent *)", newline,
                                   string "    ", Sequent.pp_sequent' gseq, newline])

      val _ = send "setup"
                   (fn () => string "  (* 5. starting search *)")

      exception Done

      val ctrs = counters ()

      val final = (case List.find (fn s => Sequent.subsumes' s gseq) axioms of
                     SOME s => (send "cfg" (fn () => string "(* goal found among axioms *)");
                                if refute then raise Fail "failed to refute!" else SOME s)
                   | _ => 
                     let
                       val table = Rules.new ()
                     in
                       List.map (Rules.add table) rules;
                       otter (OSTATE {refute = refute,
                                      maxiter = iters,
                                      table = table,
                                      sos = axioms,
                                      active = [],
                                      goal = gseq,
                                      ctrs = ctrs})
                     end)
                  
      val prf =
          (case final of
             SOME (s as Sequent.SEQUENT {chron, ...}) =>
             let
               val _ = send "validation" (fn () => hBox [string "chron: ", Chronicle.pp chron])
               val (ctx, proof, right, lx) = Timers.time1 Timers.validation Sequent.proof s
               (* val _ = send "cfg" (fn () => string "proof extracted") *)
               val isvalid = Proof.test (ctx, proof, right, lx) handle _ => false
             in
               send "validation" (fn () => hBox ([space 6,
                                                  string "final sequent [", Sequent.pp_sequent s, string "] ",
                                                  string (if isvalid then "validates" else " IS INVALID!!!"),
                                                  newline] @
                                                 (if true orelse not isvalid then 
                                                    [string "proof term: ", Proof.pp_chk proof, newline]
                                                  else [])));
               if isvalid then () else raise Invalid;
               SOME proof
             end
           | _ => NONE)
    in
      pp_ctrs ctrs;
      DB.report ();
      Option.map restore prf
    end

end
