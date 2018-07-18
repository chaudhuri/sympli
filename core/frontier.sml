(* 
 * Frontiers
 * Author: Kaustuv Chaudhuri
 *)

(* See the file frontier.sig for an explanation of frontiers and mauls *)

structure Frontier :> FRONTIER =
struct


open Lit Prop

datatype maul = Front
              | Join of maul * maul
              | Left of maul | Right of maul
              | Lax of maul


(* 
 * scan lit:
 *   list of all frontier nodes in lit
 *)
fun scan (lit as LIT {sign, skel, ...}) =
    let
      val front : lit list ref = ref []
      fun emit f = front := f :: (!front)

      fun rf (lit as LIT {skel, ...}) =
          (case skel of 
             Tensor (A, B) => (rf A; rf B)
           | One => emit lit
           | Choice (A, B) => (rf A; rf B)
           | Zero => ()
           | Bang A => ra A
           | Atomic x => if Bias.biasof x = Bias.Left then () else ra lit
           | _ => ra lit)

      and ra (lit as LIT {skel, ...}) =
          (case skel of 
             With (A, B) => (ra A; ra B)
           | Top => ()
           | Limp (A, B) => (la A; ra B)
           | Brace A => (emit A; rf A)
           | Atomic x => if Bias.biasof x = Bias.Left then emit lit else ()
           | _ => (emit lit; rf lit))

      and lf (lit as LIT {skel, ...}) =
          (case skel of
             With (A, LIT {skel = One, ...}) => la lit
           | With (A, B) => (lf A; lf B)
           | Top => ()
           | Limp (A, B) => (rf A; lf B)
           | Brace A => (emit A; lf A)
           | Atomic x => if Bias.biasof x = Bias.Right then () else la lit
           | _ => la lit)

      and la (lit as LIT {skel, ...}) =
          (case skel of 
             Tensor (A, B) => (la A; la B)
           | One => ()
           | Choice (A, B) => (la A; la B)
           | Zero => ()
           | Bang A => (emit A; lf A)
           | With (A, LIT {skel = One, ...}) => (emit A; lf A)
           | Atomic x => if Bias.biasof x = Bias.Right then emit lit else ()
           | _ => (emit lit; lf lit))
    in
      (if sign = Pos then rf else lf) lit;
      lit :: (!front)
    end

(* 
 * frontier lit = [(f1, m11), (f1, m12), ..., (f1, m1j),
 *                 (f2, m21), (f2, m22), ..., (f2, m2k),
 *                 ...
 *                 (fn, mn1), (fn, mn2), ..., (fn, mnk)]
 * 
 *    where the frontier nodes of lit are [f1, f2, ..., fn],
 *    and for each frontier node fi, the associated mauls are
 *       [mi1, mi2, ...]
 *)
fun frontier (l : lit) =
    let
      fun rmas (lit as LIT {skel, ...}) =
          (case skel of
             Tensor (A, B) =>
               let
                 val masA = rmas A
                 val masB = rmas B
               in
                 List.concat (List.map (fn maA => List.map (fn maB => Join (maA, maB)) masB) masA)
               end
           | Choice (A, B) => List.map Left (rmas A) @ List.map Right (rmas B)
           | Bang A => [Front]
           | _ => [Front])

      fun lmas (lit as LIT {skel, ...}) =
          (case skel of
             With (A, B) => List.map Left (lmas A) @ List.map Right (lmas B)
           | Limp (A, B) =>
               let
                 val masA = rmas A
                 val masB = lmas B
               in
                 List.concat (List.map (fn maA => List.map (fn maB => Join (maA, maB)) masB) masA)
               end
           | Brace A => List.map Lax (lmas A)
           | _ => [Front])

      fun mas (lit as LIT {sign, ...}) =
          (case sign of
             Pos => (lit, rmas lit)
           | Neg => (lit, lmas lit))

      val front = List.map mas (scan l)
      val front = List.concat (List.map (fn (l, ms) => List.map (fn m => (l, m)) ms) front)
    in
      front
    end

(* pretty printing *)

open P.Desc

fun pp_maul Front = string "Front"
  | pp_maul (Left m) = hBox [string "Left (", pp_maul m, string ")"]
  | pp_maul (Right m) = hBox [string "Right (", pp_maul m, string ")"]
  | pp_maul (Join (m1, m2)) = hBox [string "Join (", pp_maul m1, string ", ", pp_maul m2, string ")"]
  | pp_maul (Lax m) = hBox [string "Lax (", pp_maul m, string ")"]

end
