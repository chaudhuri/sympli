(* 
 * Derived rule generation
 * Author: Kaustuv Chaudhuri
 *)

(* See also: frontier.sig for a discussion of frontiers *)

structure RuleGen :> RULE_GEN =
struct

open Rule

structure Lit = Lit

structure Seq = Sequent
(* datatype sequent = datatype Seq.sequent *)
val ` = Seq.SEQUENT
open Seq

structure L = Label
structure LM = L.Map
open Lit Prop Frontier

structure C = Chronicle

open P.Desc

fun lpp (LIT {label, ...}) = L.pp label

datatype emode = datatype Seq.emode
fun remove em (left, l) =
    (case Seq.remove em (left, l) of
       SOME x => x
     | NONE => raise Partial)

fun linlabs (unr, aff, lin) =
    let
      fun L zone =
          LM.foldri (fn (l, n, lss) =>
                        List.tabulate (n, fn _ => l) :: lss) [] zone
    in
      List.concat (L aff @ L lin)
    end

local
  datatype sgn = POS | NEG | BOTH
                             
  fun gen_atoms M (lit as LIT {label, skel as Atomic _, sign, ...}) =
      (case LM.find (M, label) of
         SOME POS => if sign = Neg then LM.insert (M, label, BOTH) else M
       | SOME NEG => if sign = Pos then LM.insert (M, label, BOTH) else M
       | SOME BOTH => M
       | NONE => LM.insert (M, label, if sign = Pos then POS else NEG))
    | gen_atoms M (LIT {skel, ...}) = 
      (case skel of
         Tensor (A, B) => gen_atoms (gen_atoms M A) B
       | Limp (A, B) => gen_atoms (gen_atoms M A) B
       | With (A, B) => gen_atoms (gen_atoms M A) B
       | Choice (A, B) => gen_atoms (gen_atoms M A) B
       | Bang A => gen_atoms M A
       | Brace A => gen_atoms M A
       | _ => M)
in
fun atoms l =
    let
      val ats = LM.filter (fn BOTH => true | _ => false) (gen_atoms LM.empty l)
      val ats = LM.listKeys ats
    in
      ats
    end
end

exception Gen

(* specialization *)
fun spec (LIT lit) =
    let
      (* atoms that are both positively and negatively occurring *)
      val ats = atoms (LIT lit)

      (* initial sequents *)
      val inits = List.map (fn l => Conc {seq = `{left = (LM.empty, LM.empty, LM.digest [(l, 1)]),
                                                  right = (SOME l, false),
                                                  weak = false,
                                                  chron = C.Init l},
                                          prin = l}) ats

      (* is the atom P both positively and negatively occurring? *)
      fun is_both P = 
          let val lp = L.named' P
          in List.exists (fn l => L.eq (l, lp)) ats end

      fun lax {left, right = (_, lx), weak, chron} = lx

      (* focus (l, ma) = rule for frontier literal l of maul ma *)
      fun focus (l, ma) = SOME (focus' (l, ma)) handle Gen => NONE

      and focus' (lit as LIT {label, sign = Pos, ...}, ma) =
            rf lit ma (fn {left, right, weak, chron} =>
                          Conc {seq = `{left = left,
                                        right = (SOME label, false),
                                        weak = weak,
                                        chron = chron},
                                prin = label})
        | focus' (lit as LIT {label, sign = Neg, mode = ref mode, ...}, ma) =
          (case mode of
             Lit.NORMAL => 
               lf lit ma (fn {left, right, weak, chron} =>
                             Conc {seq = `{left = Seq.join' (left, label),
                                           right = right,
                                           weak = weak,
                                           chron = chron},
                                   prin = label})
           | Lit.HEAVY => 
               lf lit ma (fn sA =>
                             Conc {seq = `{left = Seq.join (#left sA, (LM.digest [(label, 1)], LM.empty, LM.empty)),
                                           right = #right sA,
                                           weak = #weak sA,
                                           chron = C.Copy (label, #chron sA)},
                                   prin = label})
           | Lit.AFFINE => 
               lf lit ma (fn sA =>
                             Conc {seq = `{left = Seq.join (#left sA, (LM.empty, LM.digest [(label, 1)], LM.empty)),
                                           right = #right sA,
                                           weak = #weak sA,
                                           chron = #chron sA},
                                   prin = label}))


      (* right focal *)
      and rf (lit as LIT {label, skel, ...}) ma k =
          (case (skel, ma) of
             (Tensor (A, B), Join (m1, m2)) => 
               rf A m1 (fn sA =>
                           if lax sA then raise Partial
                           else 
                             rf B m2 (fn sB =>
                                         if lax sB then raise Partial
                                         else 
                                           k {left = Seq.join (#left sA, #left sB),
                                              right = (SOME label, false),
                                              weak = #weak sA orelse #weak sB,
                                              chron = C.TensR (linlabs (#left sA), #chron sA, #chron sB)}))
           | (One, Front) => 
               k {left = (LM.empty, LM.empty, LM.empty),
                  right = (SOME label, false),
                  weak = false,
                  chron = C.OneR}
           | (Choice (A, B), Left ma) => 
               rf A ma (fn sA => 
                           if lax sA then raise Partial
                           else 
                             k {left = #left sA,
                                right = (SOME label, false),
                                weak = #weak sA,
                                chron = C.ChoiceR1 (#chron sA)})
           | (Choice (A, B), Right ma) => 
               rf B ma (fn sB =>
                           if lax sB then raise Partial
                           else 
                             k {left = #left sB, 
                                right = (SOME label, false),
                                weak = #weak sB,
                                chron = C.ChoiceR2 (#chron sB)})
           | (Bang A, Front) =>
               ra A [] (fn s as {left as (unr, aff, lin), chron, ...} =>
                           if lax s orelse not (LM.isEmpty aff andalso LM.isEmpty lin) then raise Partial
                           else k {left = left,
                                   right = (SOME label, false),
                                   weak = false,
                                   chron = C.BangR chron})
           | (Atomic P, _) => 
               if Bias.biasof P = Bias.Left then
                 if not (is_both P) then raise Gen
                 else k {left = Seq.join' ((LM.empty, LM.empty, LM.empty), label),
                         right = (SOME label, false),
                         weak = false,
                         chron = C.Init label}
               else ra lit [] k
           | (_, Front) => ra lit [] k)

      (* right active *)
      and ra (lit as LIT {label, skel, ...}) rel k =
          (case skel of
             With (A, B) => 
               ra A rel (fn sA =>
                            if lax sA then raise Partial
                            else 
                              ra B rel (fn sB => 
                                           if lax sB then raise Partial
                                           else 
                                             k {left = Seq.add ((#left sA, #weak sA), (#left sB, #weak sB)),
                                                right = (SOME label, false),
                                                weak = #weak sA andalso #weak sB,
                                                chron = C.WithR (#chron sA, #chron sB)}))
           | Top => 
               k {left = (LM.empty, LM.empty, LM.empty),
                  right = (SOME label, false),
                  weak = true,
                  chron = C.TopR}
           | Limp (A, B) => 
               ra B (A :: rel) (fn sB =>
                                   if lax sB then raise Partial
                                   else 
                                     k {left = #left sB,
                                        right = (SOME label, false),
                                        weak = #weak sB,
                                        chron = C.LimpR (#chron sB)})
           | Brace A => 
               la ((SOME A, true), []) rel
                  (fn sA =>
                      k {left = #left sA,
                         right = (SOME label, false),
                         weak = #weak sA,
                         chron = C.BraceR (#chron sA)})
           | _ => la ((SOME lit, false), []) rel k)


      (* left focal *)
      and lf (lit as LIT {label, skel, ...}) ma k =
          (case (skel, ma) of
             (With (_, LIT {skel = One, ...}), Front) => la ((NONE, false), []) [lit] k
           | (With (A, B), Left ma) => 
               lf A ma (fn sA =>
                           k {left = #left sA, right = #right sA, weak = #weak sA,
                              chron = C.WithL1 (label, #chron sA)})
           | (With (A, B), Right ma) => 
               lf B ma (fn sB =>
                           k {left = #left sB, right = #right sB, weak = #weak sB,
                              chron = C.WithL2 (label, #chron sB)})
           | (Limp (A, B), Join (ma1, ma2)) => 
               rf A ma1 (fn sA =>
                            lf B ma2 (fn sB =>
                                         k {left = Seq.join (#left sA, #left sB),
                                            right = #right sB,
                                            weak = #weak sA orelse #weak sB,
                                            chron = C.LimpL (linlabs (#left sA), label, #chron sA, #chron sB)}))
           | (Brace A, Lax ma) => 
               la ((NONE, true), []) [A]
                  (fn s =>
                      (Comm.send "la" (fn () => string "cleared braceL");
                       k {left = #left s,
                          right = (#1 (#right s), true),
                          weak = #weak s,
                          chron = C.BraceL (label, #chron s)}))
           | (Atomic P, Front) => 
               if Bias.biasof P = Bias.Right then 
                 if not (is_both P) then raise Gen
                 else k {left = (LM.empty, LM.empty, LM.empty),
                         right = (SOME label, false),
                         weak = false,
                         chron = C.Init label}
               else la ((NONE, false), []) [lit] k
           | (_, Front) => la ((NONE, false), []) [lit] k)

      (* left active *)
      and la (rs, ls) ((lit as LIT {label, skel, ...}) :: lits) k =
          (case skel of
             Tensor (A, B) => 
               la (rs, ls) (A :: B :: lits)
                  (fn s => 
                      k {left = #left s,
                         right = #right s,
                         weak = #weak s,
                         chron = C.TensL (label, #chron s)})
           | One => 
               la (rs, ls) lits
                 (fn s =>
                     k {left = #left s, right = #right s, weak = #weak s, chron = C.OneL (label, #chron s)})
           | Choice (A, B) => 
               let
                 fun  right_add ((L1, b1), (L2, b2)) =
                      let
                        fun radd (NONE, NONE) = NONE
                          | radd (SOME l, NONE) = SOME l
                          | radd (NONE, SOME l) = SOME l
                          | radd (SOME l1, SOME l2) = 
                              if L.eq (l1, l2) then SOME l1 else raise Partial
                      in
                        (radd (L1, L2), b1 orelse b2)
                      end
               in
                 la (rs, ls) (A :: lits)
                    (fn sA => 
                        la (rs, ls) (B :: lits)
                           (fn sB =>
                               k {left = Seq.add ((#left sA, #weak sA), (#left sB, #weak sB)),
                                  right = right_add (#right sA, #right sB),
                                  weak = #weak sA andalso #weak sB,
                                  chron = C.ChoiceL (label, #chron sA, #chron sB)}))
               end
           | Zero => 
               k {left = (LM.empty, LM.empty, LM.empty),
                  right = (NONE, false),
                  weak = true,
                  chron = C.ZeroL label}
           | _ => la (rs, lit :: ls) lits k)
          
        (* the following is the only case where a premiss is required *)
        | la ((rs, rlx), ls) [] k =
          let
            fun right_matches weak (L1, (L2, lx)) =
                let
                  fun rmat weak (NONE, r) = ((r, rlx), false)
                    | rmat weak (SOME (LIT {label, ...}), SOME r) = 
                        if L.neq (label, r) then raise Partial
                        else ((SOME r, rlx), weak)
                    | rmat false _ = raise Partial
                    | rmat true (SOME (LIT {label, ...}), NONE) = 
                        ((SOME label, rlx), false)

                  fun imp (a, b) = not a orelse b
                in
                  if imp (lx, rlx) then rmat weak (L1, L2)
                  else (Comm.send "la" (fn () => string "oopsie");
                        raise Partial)
                end

            fun extract_all (false, _) (ls, left) = 
                (* everything must be normally extracted *)
                List.foldr (fn (l, (left, refl)) =>
                               let
                                 val {left, refl = refl', ...} = remove NORMAL (left, l)
                               in
                                 (left, refl' o refl)
                               end) (left, fn c => c) ls
              | extract_all (true, llax) (ls, left) = 
                (* if llax, then all of ls can be laxly extracted; otherwise at
                 * least one of ls must be normal *)
                let
                  val (left, refl, fresh) =
                      List.foldr (fn (l, (left, refl, fresh)) =>
                                     let
                                       val {left, refl = refl', fresh = fresh'} = remove LAX (left, l)
                                     in
                                       (left, refl' o refl, fresh' andalso fresh)
                                     end) (left, fn c => c, true) ls
                in
                  if not llax andalso fresh then raise Partial
                  else (left, refl)
                end
          in
            Par (fn s as Seq.SEQUENT {left, right, weak, chron} =>
                    let
                      val _ = Comm.send "la" (fn () => hBox (string "needs: " ::
                                                             P.delimit [string ", "] (fn LIT {label, ...} => Label.pp label) ls @
                                                             [string " ==> ",
                                                              (case rs of 
                                                                 NONE =>string "."
                                                               | SOME (LIT {label, ...}) => Label.pp label)] @
                                                              (if rlx then [string " lax"] else[])))

                      (* first see if the right hand side is OK *)
                      val (right, llax) = right_matches weak (rs, right)
                      val _ = Comm.send "la" (fn () => string "right matched!")
                      val (left, refl) = extract_all (weak, llax) (ls, left)
                      val _ = Comm.send "la" (fn () => string "extraction succeeded!")

                      val s = {left = left,
                               right = right,
                               weak = weak,
                               chron = refl chron}
                    in 
                      Comm.send "la" (fn () => hBox [string "constructed: ", Sequent.pp_sequent (Sequent.SEQUENT s)]);
                      k s
                    end)
          end

      val front = frontier (LIT lit)
      val rules = List.mapPartial focus front
    in
      (* inits @ *) rules
    end

end
