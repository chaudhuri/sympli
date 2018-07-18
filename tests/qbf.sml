(* 
 * Simple compiler for qbfs
 * Author: Kaustuv Chaudhuri
 * Added: Sat Jul  3 17:40:40 EDT 2004
 *)

signature QBF =
sig

type var

datatype mat = And of mat * mat | Top
             | Or of mat * mat  | Bot
             | Imp of mat * mat
             | Not of mat
             | Var of var
                      
(* Prenex quantified boolean formula, using HOAS *)
datatype qbf = All of var -> qbf
             | Ex of var -> qbf
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

datatype mat = And of mat * mat | Top
             | Or of mat * mat  | Bot
             | Imp of mat * mat
             | Var of var
             | Not of mat

datatype qbf = All of var -> qbf
             | Ex of var -> qbf
             | Mat of mat

local val store = ref 1 in
fun reset () = store := 1
fun fresh pref = pref ^ Int.toString (!store) before store := !store + 1
end

fun compile Q =
    let
      val (matrix, quant, copy) = (ref [], ref [], ref [])
      fun emit w f = w := f :: (!w)

      val _ = reset ()

      fun cmat (And (A, B)) =
          let val M = fresh "M" in
            M before emit matrix (cmat A ^ " * " ^ cmat B ^ " -o " ^ M)
          end
        | cmat Top = "1"
        | cmat (Or (A, B)) =
          let val M = fresh "M" in
            M before emit matrix (cmat A ^ " + " ^ cmat B ^ " -o " ^ M)
          end
        | cmat Bot = "0"
        | cmat (Var v) = v
        | cmat (Imp (A, B)) = cmat (Or (Not A, B))
        | cmat (Not A) = cnot A

      and cnot (And (A, B)) = cmat (Or (Not A, Not B))
        | cnot Top = cmat Bot
        | cnot (Or (A, B)) = cmat (And (Not A, Not B))
        | cnot Bot = cmat Top
        | cnot (Imp (A, B)) = cmat (And (A, Not B))
        | cnot (Var v) = v ^ "'"
        | cnot (Not A) = cmat A

      fun cqbf q (Mat f) = "q" ^ Int.toString q ^ " * " ^ cmat f
        | cqbf q (All F) = quantified ("+", q) F
        | cqbf q (Ex F) = quantified ("&", q) F

      and quantified (oper, q) F =
          let
            val X = fresh "X"
            val X' = X ^ "'"
            val qq = "q" ^ Int.toString q
            val qq' = "q" ^ Int.toString (q + 1)
          in
            emit quant (qq ^ " -o (" ^ qq' ^ " * " ^ X ^ ") " ^ oper ^ " (" ^ qq' ^ " * " ^ X' ^ ")");
            emit copy (X ^ " -o " ^ X ^ " * " ^ X);
            emit copy  (X' ^ " -o " ^ X' ^ " * " ^ X');
            cqbf (q + 1) (F X)
          end
            

      val r = cqbf 0 Q

      val ret = "\t(* goal *)\nq0 -o " ^ r ^ " * #.\n"
      val ret = "\t(* quantifier prefix *)\n" ^ 
                List.foldl (fn (pr, r) => "(" ^ pr ^ ") -o \n" ^ r) ret (!quant)
      val ret = "\t(* matrix *)\n" ^ 
                List.foldl (fn (pr, r) => "(" ^ pr ^ ") -o \n" ^ r) ret (!matrix)
      val ret = "\t(* input branching *)\n" ^ 
                List.foldl (fn (pr, r) => "(" ^ pr ^ ") -> \n" ^ r) ret (!copy)
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

(* comments are in UTF-8 for no good reason *)

(* ∀X. ∃Y. X ⊃ Y *)
val q0 = All (fn X => Ex (fn Y => Mat (Imp (Var X, Var Y))))

(* ∀X. ∃Y. X ≡ Y *)
val q1 = All (fn X => Ex (fn Y => Mat (And (Imp (Var X, Var Y),
                                            Imp (Var Y, Var X)))))

(* ∃X. ∀Y. X ≡ Y *)
val q2 = Ex (fn X => All (fn Y => Mat (And (Imp (Var X, Var Y),
                                            Imp (Var Y, Var X)))))

(* ∃X. X ∧ X *)
val q3 = Ex (fn X => Mat (And (Var X, Var X)))

(* ∀X. ∀Y. ∀Z. [[X ⊃ Y] ∧. Y ⊃ Z] ⊃. X ⊃ Z *)
val q4 = All (fn X => 
                 All (fn Y =>
                         All (fn Z =>
                                 Mat (Imp (And (Imp (Var X, Var Y),
                                                Imp (Var Y, Var Z)),
                                           Imp (Var X, Var Z))))))

(* ∀X. ∀Y. [X ⊃ Y] ∨. Y ⊃ X *)
val q5 = All (fn X => All (fn Y => Mat (Or (Imp (Var X, Var Y),
                                            Imp (Var Y, Var X)))))

(* ∃X. ∀Y. X ⊃ Y *)
val q6 = Ex (fn X => All (fn Y => Mat (Imp (Var X, Var Y))))

end

end

(* 
 * Local Variables:
 * buffer-file-coding-system: utf-8
 * End:
 *)
