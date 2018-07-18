(* 
 * Simple copy-free compiler for qbfs in MAELL
 * Author: Kaustuv Chaudhuri
 * Added: Sat Jul  3 17:40:40 EDT 2004
 *)

signature QBF =
sig

type var

(* matrix in NNF *)
datatype mat = And of mat * mat         (* conjunction *)
              | Or of mat * mat         (* disjunction *)
              | Pos of var              (* positive literal *)
              | Neg of var              (* negative literal *)

(* uses HOAS *)
datatype qbf = Forall of var -> qbf
             | Exists of var -> qbf
             | Mat of mat

(* compile a qbf to a proposition *)
val compile : qbf -> string

(* convenience: write to a file *)
datatype oper = Prove | Refute
val write : string -> (oper * qbf) -> unit

end



structure Qbf :> QBF =
struct

type var = string

datatype mat = And of mat * mat
              | Or of mat * mat
              | Pos of var
              | Neg of var

datatype qbf = Forall of var -> qbf
             | Exists of var -> qbf
             | Mat of mat

local val store = ref 1 in
fun reset () = store := 1
fun fresh pref = pref ^ Int.toString (!store) before store := !store + 1
end

fun compile Q =
    let
      val (matrix, quant) = (ref [], ref [])
      fun emit w f = w := f :: (!w)

      val _ = reset ()

      fun cmat (And (A, B)) =
          let val M = fresh "M" in
            M before emit matrix (cmat A ^ " * " ^ cmat B ^ " -o " ^ M)
          end
        | cmat (Or (A, B)) =
          let val M = fresh "M" in
            M before emit matrix (cmat A ^ " + " ^ cmat B ^ " -o " ^ M)
          end
        | cmat (Pos v) = v
        | cmat (Neg v) = v ^ "'"

      fun cqbf q (Mat f) = "q" ^ Int.toString q ^ " * " ^ cmat f
        | cqbf q (Forall F) = quantified ("+", q) F
        | cqbf q (Exists F) = quantified ("&", q) F

      and quantified (oper, q) F =
          let
            val X = fresh "X"
            val X' = X ^ "'"
            val qq = "q" ^ Int.toString q
            val qq' = "q" ^ Int.toString (q + 1)
          in
            emit quant (qq ^ " -o (" ^ qq' ^ " * !" ^ X ^ ") " ^ oper ^ " (" ^ qq' ^ " * !" ^ X' ^ ")");
            cqbf (q + 1) (F X)
          end
            

      val r = cqbf 0 Q

      val ret = "\t(* goal *)\nq0 -o " ^ r ^ " * #.\n"
      val ret = "\t(* quantifier prefix *)\n" ^ 
                List.foldl (fn (pr, r) => "(" ^ pr ^ ") -o \n" ^ r) ret (!quant)
      val ret = "\t(* matrix *)\n" ^ 
                List.foldl (fn (pr, r) => "(" ^ pr ^ ") -o \n" ^ r) ret (!matrix)
    in
      ret
    end

datatype oper = Prove | Refute
fun write f (oper, Q) =
    let
      val file = TextIO.openOut f
      fun oup s = TextIO.output (file, s ^ "\n")
    in
      oup "%log timers : highlevel.";
      oup "";
      oup ("%" ^ (if oper = Prove then "prove\n" else "refute\n") ^ compile Q);
      TextIO.closeOut file
    end

end



(* some simple qbfs *)
structure Qs =
struct

local open Qbf in

(* ALL X. EX Y. X => Y *)
val q0 = Forall (fn X => Exists (fn Y => Mat (Or (Neg X, Pos Y))))

(* ALL X. EX Y. X <=> Y *)
val q1 = Forall (fn X => Exists (fn Y => Mat (And (Or (Neg X, Pos Y),
                                                   Or (Neg Y, Pos X)))))

(* EX X. ALL Y. X <=> Y *)
val q2 = Exists (fn X => Forall (fn Y => Mat (And (Or (Neg X, Pos Y),
                                                   Or (Neg Y, Pos X)))))

(* ALL X. ALL Y. ALL Z. (X => Y) & (Y => Z) => (X => Z) *)
val q4 = Forall
           (fn X =>
               Forall
                 (fn Y =>
                     Forall
                       (fn Z =>
                           Mat (Or (Or (And (Pos X, Neg Y),
                                        And (Pos Y, Neg Z)),
                                    Or (Neg X, Pos Z))))))
end

end
