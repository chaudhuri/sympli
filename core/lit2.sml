(* 
 * Two-phase labelling
 * Author: Kaustuv Chaudhuri
 *)

structure Lit :> LIT =
struct

datatype sign = Pos | Neg

fun flip Pos = Neg
  | flip Neg = Pos


structure L = Label
structure LM = L.Map

open Prop

(* literals *)
datatype lit = LIT of {label : Label.label,  (* name of literal *)
                       skel : skel,          (* skeleton *)
                       gen : bool,           (* this label has a rule? *)
                       sign : sign}
withtype skel = lit Prop.skel

fun eq_lit (LIT L1, LIT L2) =
      eq_skel (#skel L1, #skel L2)
      andalso #sign L1 = #sign L2
      
and eq_skel (s1, s2) = Prop.eq_skel eq_lit (s1, s2)

fun named (l, s, k) = LIT {label = l,
                           sign = s,
                           skel = k,
                           gen = true}

fun anon (s, k) = LIT {label = L.new (),
                       sign = s,
                       skel = k,
                       gen = false}

fun skel (LIT {skel, ...}) = skel
fun sign (LIT {sign, ...}) = sign

val trivlab = L.named "__TRIVIAL__"
fun triv (Prop A) =
    let
      fun skel (Atomic P) = Atomic P
        | skel (Tensor (A, B)) = Tensor (triv A, triv B)
        | skel One = One
        | skel (Limp (A, B)) = Limp (triv A, triv B)
        | skel (With (A, B)) = With (triv A, triv B)
        | skel Top = Top
        | skel (Choice (A, B)) = Choice (triv A, triv B)
        | skel Zero = Zero
        | skel (Bang A) = Bang (triv A)
    in
      LIT {label = trivlab, skel = skel A, gen = true, sign = Pos}
    end

fun triv' p =
    let val LIT {skel, ...} = triv p in skel end


(* 
 * Left passive phase                                 
 *                                                    
 *    input          |  operation                     
 *  -----------------+------------------------------- 
 *    P, #           |  label                         
 *    -o, &          |  descend (same phase)          
 *    *, 1, +, 0, !  |  transition to left-active     
 *)
fun lpass (Prop A) =
    let
      fun label (Atomic P) = named (L.named' P, Neg, Atomic P)
        | label (Limp (B, C)) = anon (Neg, Limp (rpass B, lpass C))
        | label (With (B, C)) = anon (Neg, With (lpass B, lpass C))
        | label Top = named (L.new (), Neg, Top)
        | label _ = lact (Prop A)
    in
      label A
    end


(* 
 * Right passive phase                                 
 *                                                    
 *    input          |  operation                     
 *  -----------------+------------------------------- 
 *    P, 1, 0        |  label                         
 *    *, +, !        |  descend (same phase)
 *    -o, &, #       |  transition to right-active
 *)
and rpass (Prop A) =
    let
      fun label (Atomic P) = named (L.named' P, Pos, Atomic P)
        | label (Tensor (B, C)) = anon (Pos, Tensor (rpass B, rpass C))
        | label One = named (L.new (), Pos, One)
        | label (Choice (B, C)) = anon (Pos, Choice (rpass B, rpass C))
        | label Zero = named (L.new (), Pos, Zero)
        | label (Bang B) = anon (Pos, Bang (rpass B))
        | label _ = ract (Prop A)
    in
      label A
    end

(* 
 * Left active phase                                 
 *                                                    
 *    input          |  operation                     
 *  -----------------+------------------------------- 
 *    1, 0           |  label
 *    *, +, !        |  descend (same phase)
 *    P, -o, &, #    |  label and 
 *                   |    transition to left-passive
 *)
and lact (Prop A) = 
    let
      fun label (Tensor (B, C)) = anon (Neg, Tensor (lact B, lact C))
        | label One = named (L.new (), Neg, One)
        | label (Choice (B, C)) = anon (Neg, Choice (lact B, lact C))
        | label Zero = named (L.new (), Neg, Zero)
        | label (Bang B) = anon (Neg, Bang (lact B))
        | label _ = 
          let
            val l = (case A of
                       Atomic P => L.named' P
                     | _ => L.new ())
          in
            named (l, Neg, skel (lpass (Prop A)))
          end
    in
      label A
    end

(* 
 * Right active phase                                 
 *                                                    
 *    input             |  operation                     
 *  --------------------+------------------------------- 
 *    #                 |  label
 *    -o, &             |  descend (same phase)
 *    P, *, 1, +, 0, !  |  label and 
 *                      |    transition to right-passive
 *)
and ract (Prop A) =
    let
      fun label (Limp (B, C)) = anon (Pos, Limp (lact B, ract C))
        | label (With (B, C)) = anon (Pos, With (ract B, ract C))
        | label Top = named (L.new (), Pos, Top)
        | label _ = 
          let
            val l = (case A of
                       Atomic P => L.named' P
                     | _ => L.new ())
          in
            named (l, Pos, skel (rpass (Prop A)))
          end
    in
      label A
    end


structure Register =
  struct
    open L.Map

    val reg : skel L.map ref = ref empty
    fun reset () = reg := empty

    fun bind (l, skel) = reg := insert (!reg, l, skel)

    fun lookup l = if L.is_named l then SOME (Atomic (L.name l))
                   else find (!reg, l)
  end
structure R = Register

(* 
 * Label A with specified sign.
 * 
 *   If:  lm = label (A, sign),
 * Then:  for every (l, lit) in lm, 
 *     1. lit is (left- or right-) passive,
 *          or the label of the goal A.
 *     2. If lit is not the goal A,
 *         then it is an operand of an active connective.
 *)
fun label (A, sign) =
    let
      val names : lit list ref = ref []
      val atoms : lit list ref = ref []

      fun emit (lit as LIT {label, skel, ...}) =
          (if L.is_named label then atoms := lit :: (!atoms)
           else (names := lit :: (!names); R.bind (label, skel)))

      fun pluck (lit as LIT {skel, gen, ...}) =
            pluck' skel before (if gen then emit lit else ())

      and pluck' (Tensor (A, B)) = (pluck A; pluck B)
        | pluck' (Limp (A, B)) = (pluck A; pluck B)
        | pluck' (With (A, B)) = (pluck A; pluck B)
        | pluck' (Choice (A, B)) = (pluck A; pluck B)
        | pluck' (Bang A) = pluck A
        | pluck' _ = ()
    
      val lit = named (L.new (), sign, skel ((case sign of Pos => rpass | Neg => lpass) A))
    in
      pluck lit;
      {goal = lit, labs = !names, atoms = !atoms}
    end


(* pretty printing *)
open P.Desc

fun pp (LIT {label, skel, sign, gen}) =
      hBox [Label.pp label, string " = {",
            hvBox (P.Rel 0,
                   [pp_skel skel, string ";", space 1, pp_sign sign, cut]),
            string "}"]

and itemize_lit (LIT {label, gen, skel, ...}) =
      if gen then P.Atm (Label.pp label)
      else itemize_skel itemize_lit skel

and pp_sign Pos = string "+"
  | pp_sign Neg = string "-"

and pp_skel skel = P.lineate (itemize_skel itemize_lit skel)

end
