(* 
 * Basic rule generation
 * Author: Kaustuv Chaudhuri
 *)

(* for comments on rules, see doc/rules.tex *)

structure Rule :> 
          RULE where type Lit.lit = Lit.lit =
struct

structure Lit = Lit

structure Seq = Sequent
datatype sequent = datatype Seq.sequent

structure L = Label
structure LM = L.Map
open Lit Prop

structure C = Chronicle

exception Partial

val ` = Seq.SEQUENT

open P.Desc

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


(* conclusion of fully instantiated rules *)
type conc = {seq : sequent, prin : L.label}

datatype rule = Par of Sequent.sequent -> rule
              | Conc of conc

fun apply (Conc c) s = NONE
  | apply (Par f) s = SOME (f s)

fun is_conc (Conc _) = true
  | is_conc _ = false

(* initial sequents *)

fun init (plit as LIT L) =
      {seq = `{left = (LM.empty, LM.empty, LM.digest [(#label L, 1)]),
               right = SOME (#label L),
               weak = false,
               chron = C.Init (#label L)},
       prin = #label L}


(* other judgemental rules *)

fun copy (lit as LIT L) =
      Par (fn SEQUENT seq =>
               case Seq.remove STRICT (#left seq, lit) of
                 NONE => raise Partial
               | SOME {left, refl} => 
                   Conc {seq = `{left = Seq.join (left, (LM.digest [(#label L, 1)], LM.empty, LM.empty)),
                                 right = #right seq,
                                 weak = #weak seq,
                                 chron = C.Copy (#label L, refl (#chron seq))},
                         prin = #label L})

fun promote (lit as LIT L) =
      Par (fn SEQUENT seq =>
               case Seq.remove STRICT (#left seq, lit) of
                 NONE => raise Partial
               | SOME {left, refl} =>
                   Conc {seq = `{left = Seq.join (left, (LM.empty, LM.digest [(#label L, 1)], LM.empty)),
                                 right = #right seq,
                                 weak = #weak seq,
                                 chron = refl (#chron seq)},
                         prin = #label L})

(* multiplicative right *)

fun tensor_R (plit as LIT L) (LIT LA, LIT LB) =
      Par (fn SEQUENT seq1 =>
              case #right seq1 of
                NONE => raise Partial
              | SOME l1 => if L.neq (#label LA, l1) then raise Partial
                           else Par (fn SEQUENT seq2 =>
                                        case #right seq2 of
                                          NONE => raise Partial
                                        | SOME l2 => if L.neq (#label LB, l2) then raise Partial
                                                     else Conc {seq = `{left = Seq.join (#left seq1, #left seq2),
                                                                        right = SOME (#label L),
                                                                        weak = #weak seq1 orelse #weak seq2,
                                                                        chron = C.TensR (linlabs (#left seq1),
                                                                                         #chron seq1, #chron seq2)},
                                                                prin = #label L}))

      
fun one_R (plit as LIT L) =
      Conc {seq = `{left = (LM.empty, LM.empty, LM.empty),
                    right = SOME (#label L),
                    weak = false,
                    chron = C.OneR},
            prin = #label L}


fun limp_R (plit as LIT L) (LIT LA, LIT LB) =
      Par (fn SEQUENT seq =>
               case #right seq of
                 NONE =>                          (* [INV] #weak seq = true *)
                   let
                     val {left, refl} = remove NORMAL (#left seq, LIT LA)
                   in
                     Conc {seq = `{left = left, 
                                   right = SOME (#label L),
                                   weak = true,
                                   chron = C.LimpR (refl (#chron seq))},
                           prin = #label L}
                    end
               | SOME L' =>
                   if L.neq (L', #label LB)
                   then raise Partial
                   else
                     let
                       (* if weak, then A need not be present strictly; otherwise it must be there *)
                       val {left, refl} = remove (if #weak seq then LAX else NORMAL)
                                                 (#left seq, LIT LA)
                     in 
                       Conc {seq = `{left = left,
                                     right = SOME (#label L),
                                     weak = #weak seq,
                                     chron = C.LimpR (refl (#chron seq))},
                             prin = #label L}
                     end)


(* multiplicative left *)

fun tensor_L (plit as LIT L) (LIT LA, LIT LB) =
      Par (fn SEQUENT seq =>
               let
                 fun get (la, ema) (lb, emb) =
                     let
                       val {left, refl = refl1} = remove ema (#left seq, la)
                       val {left, refl = refl2} = remove emb (left, lb)
                       val refl = refl2 o refl1
                     in
                       (left, refl)
                     end

                 val (left, refl) =
                     if #weak seq then
                       (get (LIT LA, NORMAL) (LIT LB, LAX)
                        handle Partial => get (LIT LA, LAX) (LIT LB, NORMAL))
                     else get (LIT LA, NORMAL) (LIT LB, NORMAL)
               in
                 Conc {seq = `{left = Seq.join' (left, #label L),
                               right = #right seq,
                               weak = #weak seq,
                               chron = C.TensL (#label L, refl (#chron seq))},
                       prin = #label L}
               end)

fun limp_L (plit as LIT L) (LIT LA, LIT LB) =
    Par (fn SEQUENT seq1 =>
            case #right seq1 of
              NONE => raise Partial
            | SOME l => if L.neq (l, #label LA) then raise Partial
                        else 
                          Par (fn SEQUENT seq2 =>
                                  let
                                    val {left, refl} = remove NORMAL (#left seq2, LIT LB)
                                  in
                                    Conc {seq = `{left = Seq.join' (Seq.join (#left seq1, left), #label L),
                                                  right = #right seq2,
                                                  weak = #weak seq1 orelse #weak seq2,
                                                  chron = C.LimpL (linlabs (#left seq1), #label L,
                                                                   #chron seq1, refl (#chron seq2))},
                                     prin = #label L}
                                  end))

(* additive right *)

fun with_R (plit as LIT L) (LIT LA, LIT LB) =
      Par (fn SEQUENT seq1 =>
              case #right seq1 of 
                NONE => raise Partial
              | SOME l1 => if L.neq (l1, #label LA) then raise Partial
                           else 
                             Par (fn SEQUENT seq2 =>
                                     case #right seq2 of
                                       NONE => raise Partial
                                     | SOME l2 =>
                                         if L.neq (l2, #label LB) then raise Partial
                                         else 
                                           let
                                             val left =
                                                 Seq.add ((#left seq1, #weak seq1), (#left seq2, #weak seq2))
                                                 handle Seq.Add => raise Partial
                                           in
                                             Conc {seq = `{left = left,
                                                            right = SOME (#label L),
                                                            weak = #weak seq1 andalso #weak seq2,
                                                            chron = C.WithR (#chron seq1, #chron seq2)},
                                                    prin = #label L}
                                           end))

fun top_R (plit as LIT L) =
      Conc {seq = `{left = (LM.empty, LM.empty, LM.empty),
                    right = SOME (#label L),
                    weak = true,
                    chron = C.TopR},
            prin = #label L}

fun choice_R inj (plit as LIT L) (LIT L1) =
      Par (fn SEQUENT seq =>
               case #right seq of
                 SOME l => if L.eq (l, #label L1)
                           then 
                             Conc {seq = `{left = #left seq,
                                            right = SOME (#label L),
                                            weak = #weak seq,
                                            chron = inj (#chron seq)},
                                    prin = #label L}
                           else raise Partial
               | _ => raise Partial)

(* exponentials *)

fun bang_R (plit as LIT L) (LIT LA) =
      Par (fn SEQUENT seq =>
               let
                 val left as (unr, aff, lin) = #left seq
               in
                 case #right seq of
                   SOME l => if not (L.eq (l, #label LA)
                                     andalso LM.isEmpty lin
                                     andalso LM.isEmpty aff)
                             then raise Partial
                             else
                               Conc {seq = `{left = left,
                                              right = SOME (#label L),
                                              weak = false,
                                              chron = C.BangR (#chron seq)},
                                      prin = #label L}
                 | _ => raise Partial
               end)

(* additive left *)

fun with_L proj (plit as LIT L) (LIT LA) =
      Par (fn SEQUENT seq =>
               let
                 val {left, refl} = remove NORMAL (#left seq, LIT LA)
               in
                 Conc {seq = `{left = Seq.join' (left, #label L),
                                right = #right seq,
                                weak = #weak seq,
                                chron = proj (#label L, refl (#chron seq))},
                        prin = #label L}
               end)

fun right_eq (SOME l1, SOME l2) = L.eq (l1, l2)
  | right_eq _ = true

fun choice_L (plit as LIT L) (LIT LA, LIT LB) =
    let
      fun triv left l1 =
          {left = left, refl = fn ch => C.OneL (l1, ch)}
    in
      Par (fn SEQUENT seq1 =>
              let
                val {left = leftA, refl = reflA} = 
                    (case #skel LA of
                       One => triv (#left seq1) (#label LA)
                     | _ => remove NORMAL (#left seq1, LIT LA))
              in
                Par (fn SEQUENT seq2 =>
                        if not (right_eq (#right seq1, #right seq2)) then raise Partial
                        else 
                          let
                            val {left = leftB, refl = reflB} =
                                (case #skel LB of
                                   One => triv (#left seq2) (#label LB)
                                 | _ => remove NORMAL (#left seq2, LIT LB))
                                
                            val left =
                                Seq.add ((leftA, #weak seq1), (leftB, #weak seq2))
                                handle Seq.Add => raise Partial
                          in
                            Conc {seq = `{left = Seq.join' (left, #label L),
                                          right = (case #right seq1 of
                                                     SOME l => SOME l
                                                   | NONE => #right seq2),
                                          weak = #weak seq1 andalso #weak seq2,
                                          chron = C.ChoiceL (#label L, reflA (#chron seq1), reflB (#chron seq2))},
                                  prin = #label L}
                          end)
              end)
    end

fun zero_L (plit as LIT L) =
      Conc {seq = `{left = (LM.empty, LM.empty, LM.digest [(#label L, 1)]),
                    right = NONE,
                    weak = true,
                    chron = C.ZeroL (#label L)},
            prin = #label L}
    

(* specializations *)

fun announce rule (LIT L) =
      Comm.send "rules" (fn () => hBox [string "specialized ", string rule, string " for ", Label.pp (#label L)])

datatype sgn = POS | NEG | BOTH

fun gen_atoms M (lit as LIT {label, skel as Atomic P, sign, ...}) =
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
     | _ => M)


fun spec lit =
    let
      val atoms = LM.listKeys (LM.filter (fn BOTH => true | _ => false) (gen_atoms LM.empty lit))
      val inits = List.map (fn l => Conc {seq = `{left = (LM.empty, LM.empty, LM.digest [(l, 1)]),
                                                  right = SOME l,
                                                  weak = false,
                                                  chron = C.Init l},
                                          prin = l}) atoms

      val rules : rule list ref = ref []
      fun emit rule = rules := rule :: (!rules)

      fun spec' (lit as LIT {skel, sign, ...}) =
          let
            fun for (Tensor (A, B), Pos) =
                  (emit (tensor_R lit (A, B)) before announce "*R" lit; spec' A; spec' B)
              | for (Tensor (A, B), Neg) =
                  (emit (tensor_L lit (A, B)) before announce "*L" lit; spec' A; spec' B)
              | for (One, Pos) = 
                  emit (one_R lit) before announce "1R" lit
              | for (Limp (A, B), Pos) =
                  (emit (limp_R lit (A, B)) before announce "-oR" lit; spec' A; spec' B)
              | for (Limp (A, B), Neg) =
                  (emit (limp_L lit (A, B)) before announce "-oL" lit; spec' A; spec' B)
              | for (With (A, B), Pos) =
                  (emit (with_R lit (A, B)) before announce "&R" lit; spec' A; spec' B)
              | for (With (LIT A, LIT B), Neg) =
                  (case #skel B of
                     One => (emit (promote (LIT A)) before announce "promote" (LIT A); spec' (LIT A))
                   | _ => (emit (with_L C.WithL1 lit (LIT A)) before announce "&L1" (LIT A);
                           emit (with_L C.WithL2 lit (LIT B)) before announce "&L2" (LIT B);
                           spec' (LIT A); spec' (LIT B)))
              | for (Top, Pos) =
                  emit (top_R lit) before announce "#R" lit
              | for (Choice (A, B), Pos) =
                  (emit (choice_R C.ChoiceR1 lit (A)) before announce "+R1" lit;
                   emit (choice_R C.ChoiceR2 lit (B)) before announce "+R2" lit;
                   spec' A; spec' B)
              | for (Choice (A, B), Neg) =
                  (emit (choice_L lit (A, B)) before announce "+L" lit; spec' A; spec' B)
              | for (Zero, Neg) = 
                  emit (zero_L lit) before announce "0L" lit
              | for (Bang A, Pos) =
                  (emit (bang_R lit A) before announce "!R" lit; spec' A)
              | for (Bang A, Neg) =
                  (emit (copy A) before announce "copy" A; spec' A)
              | for _ = ()
          in
            for (skel, sign)
          end

    in
      spec' lit;
      inits @ (!rules)
    end

end
