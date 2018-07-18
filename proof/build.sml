(* 
 * Build terms from chronicles
 * Author: Kaustuv Chaudhuri
 *)

signature PROOF_BUILD =
sig
  type zone = (Var.var * Lit.skel) list Label.map
  val build : zone * zone * Lit.skel option -> Chronicle.chronicle -> Proof.chk
end

structure ProofBuild :> PROOF_BUILD =
struct

infixr 1 %
fun f % x = f x

open Proof
open Chronicle
open Lit

structure L = Label
structure LM = L.Map
type label = L.label

fun fresh () = Var.fresh "build"

type zone = (Var.var * lit Prop.skel) list L.map

fun remove Omega l =
    (case LM.remove (Omega, l) of
       (Omega, [(v, skel)]) => (Omega, (v, skel))
     | (Omega, (v, skel) :: vs) => (LM.insert (Omega, l, vs), (v, skel)))


fun add' Omega (v, label, skel) =
    (case LM.find (Omega, label) of
       SOME vs => LM.insert (Omega, label, (v, skel) :: vs)
     | NONE => LM.insert (Omega, label, [(v, skel)]))

fun add Omega (v, LIT {label, skel, ...}) = add' Omega (v, label, skel)

fun partition Omega sel =
    let
      fun onemore (l, (Omega1, Omega)) =
          let
            val (Omega, (v, sk)) = remove Omega l
            val Omega1 = add' Omega1 (v, l, sk)
          in
            (Omega1, Omega)
          end
    in
      List.foldr onemore (LM.empty, Omega) sel
    end

fun build (G : zone, D : zone, SOME _ : Lit.skel option) (Init l) =
    let
      val (_, (v, _)) = remove D l
    in
      Inf (Var v)
    end
  | build (G, D, g) (Copy (l, ch)) =
    let
      val (G, (v, sk)) = remove G l
      val D = add' D (v, l, sk)
      (* the following line was a MAJOR bug! --kaustuv [fixed: 2004-06-23 06:01am] *)
      val G = add' G (v, l, sk)
    in
      build (G, D, g) ch
    end
  | build (G, D, SOME (Prop.Tensor (LIT A, LIT B))) (TensR (sel, ch1, ch2)) = 
    let
      val (D1, D2) = partition D sel
      val p1 = build (G, D1, SOME (#skel A)) ch1
      val p2 = build (G, D2, SOME (#skel B)) ch2
    in
      Tensor (p1, p2)
    end
  | build (G, D, g) (TensL (l, ch)) = 
    let
      val (D, (v, Prop.Tensor (A, B))) = remove D l
      val u1 = fresh ()
      val u2 = fresh ()
      val D = add D (u1, A)
      val D = add D (u2, B)
      val p = build (G, D, g) ch
    in
      LetTens (Var v, ((u1, u2), p))
    end
  | build (G, D, SOME Prop.One) OneR = One
  | build (G, D, g) (OneL (l, ch)) =
    let
      val (D, (v, Prop.One)) = remove D l
      val p = build (G, D, g) ch
    in
      LetOne (Var v, p)
    end
  | build (G, D, SOME (Prop.Limp (A, LIT B))) (LimpR ch) = 
    let
      val u = fresh ()
      val D = add D (u, A)
      val p = build (G, D, SOME (#skel B)) ch
    in
      Lam (u, p)
    end
  | build (G, D, g) (LimpL (sel, l, ch1, ch2)) = 
    let
      val (D, (v, Prop.Limp (LIT A, B))) = remove D l
                                           handle e => (P.pr (P.Desc.string "broke LimpL"); raise e)
      val (D1, D2) = partition D sel
      val p1 = build (G, D1, SOME (#skel A)) ch1
      val u = fresh ()
      val D2 = add D2 (u, B)
      val p2 = build (G, D2, g) ch2
    in
      Let (App (Var v, p1), (u, p2))
    end
  | build (G, D, SOME (Prop.With (LIT A, LIT B))) (WithR (ch1, ch2)) = 
    let
      val p1 = build (G, D, SOME (#skel A)) ch1
      val p2 = build (G, D, SOME (#skel B)) ch2
    in
      Pair (p1, p2)
    end
  | build (G, D, g) (WithL1 (l, ch)) = 
    let
      val (D, (v, Prop.With (A, B))) = remove D l
      val u = fresh ()
      val D = add D (u, A)
      val p = build (G, D, g) ch
    in
      Let (Fst (Var v), (u, p))
    end
  | build (G, D, g) (WithL2 (l, ch)) = 
    let
      val (D, (v, Prop.With (A, B))) = remove D l
      val u = fresh ()
      val D = add D (u, B)
      val p = build (G, D, g) ch
    in
      Let (Snd (Var v), (u, p))
    end
  | build (G, D, SOME Prop.Top) TopR = Unit
  | build (G, D, SOME (Prop.Choice (LIT A, LIT B))) (ChoiceR1 ch) = 
    let
      val p = build (G, D, SOME (#skel A)) ch
    in
      Inl p
    end
  | build (G, D, SOME (Prop.Choice (LIT A, LIT B))) (ChoiceR2 ch) = 
    let
      val p = build (G, D, SOME (#skel B)) ch
    in
      Inr p
    end
  | build (G, D, g) (ChoiceL (l, ch1, ch2)) = 
    let
      val (D, (v, Prop.Choice (A, B))) = remove D l

      val u1 = fresh ()
      val D1 = add D (u1, A)
      val p1 = build (G, D1, g) ch1

      val u2 = fresh ()
      val D2 = add D (u2, B)
      val p2 = build (G, D2, g) ch2
    in
      Case (Var v, (u1, p1), (u2, p2))
    end
  | build (G, D, g) (ZeroL l) = 
    let
      val (D, (v, Prop.Zero)) = remove D l
    in
      Abort (Var v)
    end
  | build (G, D, SOME (Prop.Bang (LIT A))) (BangR ch) = 
    let
      val p = build (G, LM.empty, SOME (#skel A)) ch
    in
      Bang p
    end
  | build (G, D, g) (BangL (l, ch)) = 
    let
      val (D, (v, Prop.Bang A)) = remove D l
      val u = fresh ()
      val G = add G (u, A)
      val p = build (G, D, g) ch
    in
      LetBang (Var v, (u, p))
    end
  | build (G, D, SOME (Prop.Brace (LIT A))) (BraceR ch) = 
    let
      val p = build (G, D, SOME (#skel A)) ch
    in
      Bra p
    end
  | build (G, D, g) (BraceL (l, ch)) = 
    let
      val (D, (v, Prop.Brace A)) = remove D l
      val u = fresh ()
      val D = add D (u, A)
      val p = build (G, D, g) ch
    in
      LetBra (Var v, (u, p))
    end
end
