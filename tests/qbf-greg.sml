signature QBF =
sig

  type var
  
  datatype qbf = And of qbf * qbf | Top
               | Or  of qbf * qbf | Bot
               | Imp of qbf * qbf
               | Var of var
               | Not of qbf
               | All of var -> qbf
               | Ex of var -> qbf
  
  datatype variant = Exp | Mon
  
  datatype oper = Prove | Refute
  
  val toString : qbf -> string
  val compile : variant -> qbf -> Prop.prop
  val write : TextIO.outstream -> (qbf * variant * oper) -> unit
  val writeAll : TextIO.outstream -> (qbf * variant * oper) list -> unit
  
end

structure Qbf :> QBF =
struct
  
local open Prop in
  
  type var = string
  
  datatype qbf = And of qbf * qbf | Top
               | Or  of qbf * qbf | Bot
               | Imp of qbf * qbf
               | Var of var
               | Not of qbf
               | All of var -> qbf
               | Ex of var -> qbf
  
  datatype variant = Exp | Mon
  
  datatype oper = Prove | Refute
  
  fun ` c x = Prop (c x)
  
  local val store = ref 1 in
    fun reset () = store := 1
    fun fresh pref = pref ^ Int.toString (!store) before store := !store + 1
  end
  
  fun atom a = `Atomic (Atom.atom a)
  fun atom' a = `Atomic (Atom.atom (a ^ "'"))
  
  fun tableAnd in1 in2 out =
      let val a1 = atom in1
          val a1' = atom' in1
          val a2 = atom in2
          val a2' = atom' in2
          val oa = atom out
          val oa' = atom' out
      in `With (`Limp (a1, `Limp (a2, oa)),
         `With (`Limp (a1', `Limp (a2, oa')),
         `With (`Limp (a1, `Limp (a2', oa')),
                `Limp (a1', `Limp (a2', oa'))
         )))
      end
  
  fun tableOr in1 in2 out =
      let val a1 = atom in1
          val a1' = atom' in1
          val a2 = atom in2
          val a2' = atom' in2
          val oa = atom out
          val oa' = atom' out
      in `With (`Limp (a1, `Limp (a2, oa)),
         `With (`Limp (a1', `Limp (a2, oa)),
         `With (`Limp (a1, `Limp (a2', oa)),
                `Limp (a1', `Limp (a2', oa'))
         )))
      end
  
  fun tableImp in1 in2 out =
      let val a1 = atom in1
          val a1' = atom' in1
          val a2 = atom in2
          val a2' = atom' in2
          val oa = atom out
          val oa' = atom' out
      in `With (`Limp (a1, `Limp (a2, oa)),
         `With (`Limp (a1', `Limp (a2, oa)),
         `With (`Limp (a1, `Limp (a2', oa')),
                `Limp (a1', `Limp (a2', oa))
         )))
      end
  
  fun qvar Exp q = `Bang q
    | qvar Mon q = `Tensor (q, `Limp (q, Prop One))
  
  fun var Exp v s = `With (`Limp (atom v, atom s),
                           `Limp (atom' v, atom' s))
    | var Mon v s = `With (`Limp (atom v, `Tensor (atom v, atom s)),
                           `Limp (atom' v, `Tensor (atom' v, atom' s)))
  
  fun compile' _ s Top = atom s
    | compile' _ s Bot = atom' s
    | compile' variant s (Var v) = var variant v s
    | compile' v s (Not Q) =
        let val s' = fresh "a"
        in `Tensor (compile' v s' Q, `With (`Limp (atom s', atom' s),
                                            `Limp (atom' s', atom s)))
        end
    | compile' v s (And (Q1, Q2)) =
        let val s1 = fresh "a"
            val s2 = fresh "a"
        in `Tensor (compile' v s1 Q1, `Tensor (compile' v s2 Q2, tableAnd s1 s2 s))
        end
    | compile' v s (Or (Q1, Q2)) =
        let val s1 = fresh "a"
            val s2 = fresh "a"
        in `Tensor (compile' v s1 Q1, `Tensor (compile' v s2 Q2, tableOr s1 s2 s))
        end
    | compile' v s (Imp (Q1, Q2)) =
        let val s1 = fresh "a"
            val s2 = fresh "a"
        in `Tensor (compile' v s1 Q1, `Tensor (compile' v s2 Q2, tableImp s1 s2 s))
        end
    | compile' v s (All f) =
        let val q = fresh "q"
            val p = compile' v s (f q)
        in `Choice (`Tensor (qvar v (atom q), p),
                    `Tensor (qvar v (atom' q), p))
        end
    | compile' v s (Ex f) =
        let val q = fresh "q"
            val p = compile' v s (f q)
        in `With (`Tensor (qvar v (atom q), p),
                  `Tensor (qvar v (atom' q), p))
        end
  
  fun compile variant Q =
    let val _ = reset ()
        val s = fresh "a"
    in `Limp (compile' variant s Q, atom s)
    end
  
  fun toString' (All f) = let val x = fresh "x" in "(" ^ x ^ ") " ^ (toString' (f x)) end
    | toString' (Ex f) = let val x = fresh "x" in "[" ^ x ^ "] " ^ (toString' (f x)) end
    | toString' Top = "t"
    | toString' Bot = "f"
    | toString' (Var v) = v
    | toString' (Not Q) = "~" ^ (toString' Q)
    | toString' (And (Q1, Q2)) = "(" ^ (toString' Q1) ^ " ^ " ^ (toString' Q2) ^ ")"
    | toString' (Or (Q1, Q2)) = "(" ^ (toString' Q1) ^ " v " ^ (toString' Q2) ^ ")"
    | toString' (Imp (Q1, Q2)) = "(" ^ (toString' Q1) ^ " => " ^ (toString' Q2) ^ ")"
    
  fun toString Q =
    let val _ = reset ()
    in toString' Q
    end
  
  fun write stream (Q, variant, oper) =
    let val qstr = toString Q
        val opstr = case oper of Prove => "prove" | Refute => "refute"
        val qprop = compile variant Q
        val propstr = P.unparse (Prop.pp_prop qprop)
    in TextIO.output (stream, "(* " ^ qstr ^ " *)\n\n");
       TextIO.output (stream, "%" ^ opstr ^ " " ^ propstr ^ ".\n\n")
    end
  
  fun writeAll stream l = List.app (write stream) l;
  
end
  
end

structure Qs =
struct

local open Qbf in

(* [x] x *)
val q0 = Ex (fn X => Var X)

(* [x] ~x *)
val q1 = Ex (fn X => Not (Var X))

(* [x] ~~x *)
val q2 = Ex (fn X => Not (Not (Var X)))

(* [x] (x ^ x) *)
val q3 = Ex (fn X => And (Var X, Var X))

(* [x] (x v x) *)
val q4 = Ex (fn X => Or (Var X, Var X))

(* (x) (x => x) *)
val q5 = All (fn X => Imp (Var X, Var X))

(* (x) (x v ~x) *)
val q6 = All (fn X => Or (Var X, Not (Var X)))

(* (x) (~x v ~~x) *)
val q7 = All (fn X => Or (Not (Var X), Not (Not (Var X))))

(* (x) [y] (~x v y) *)
val q8 = All (fn X => Ex (fn Y => Or (Not (Var X), Var Y)))

(* (x) [y] (x => y) *)
val q9 = All (fn X => Ex (fn Y => Imp (Var X, Var Y)))

(* [x] (y) (~x v y) *)
val q10 = Ex (fn X => All (fn Y => Or (Not (Var X), Var Y)))

(* [x] (y) (x => y) *)
val q11 = Ex (fn X => All (fn Y => Imp (Var X, Var Y)))

(* (x) (y) (x => (y => x)) *)
val q12 = All (fn X => All (fn Y => Imp (Var X, Imp (Var Y, Var X))))

(* (x) (y) (z) ((x => y => z) => (x => y) => x => z) *)
(*
val q13 = All (fn X => All (fn Y => All (fn Z =>
        Imp (Imp (Var X, Imp (Var Y, Var Z)),
             Imp (Imp (Var X, Var Y),
                  Imp (Var X, Var Z))))))
*)

(* (x) [y] ((x => y) ^ (y => x)) *)
val q14 = All (fn X => Ex (fn Y => And (Imp (Var X, Var Y),
                                        Imp (Var Y, Var X))))

(* [y] (x) ((x => y) ^ (y => x)) *)
val q15 = Ex (fn X => All (fn Y => And (Imp (Var X, Var Y),
                                        Imp (Var Y, Var X))))

(* (x) (y) (z) ((x => y) ^ (y => z) => (x => z)) *)
val q16 = All (fn X =>
                 All (fn Y =>
                         All (fn Z =>
                                 Imp (And (Imp (Var X, Var Y),
                                           Imp (Var Y, Var Z)),
                                      Imp (Var X, Var Z)))))

(* (x) (y) ((x => y) v (y => x)) *)
val q17 = All (fn X => All (fn Y => Or (Imp (Var X, Var Y),
                                        Imp (Var Y, Var X))))

val all = [(q1, Exp, Prove), (q1, Mon, Prove),
           (q2, Exp, Prove), (q2, Mon, Prove),
           (q3, Exp, Prove), (q3, Mon, Prove),
           (q4, Exp, Prove), (q4, Mon, Prove),
           (q5, Exp, Prove), (q5, Mon, Prove),
           (q6, Exp, Prove), (q6, Mon, Prove),
           (q7, Exp, Prove), (q7, Mon, Prove),
           (q8, Exp, Prove), (q8, Mon, Prove),
           (q9, Exp, Prove), (q9, Mon, Prove),
           (q10, Exp, Prove), (q10, Mon, Prove),
           (q11, Exp, Prove), (q11, Mon, Prove),
           (q12, Exp, Prove), (q12, Mon, Prove),
(*           (q13, Exp, Prove), (q13, Mon, Prove), *)
           (q14, Exp, Prove), (q14, Mon, Prove),
           (q15, Exp, Refute), (q15, Mon, Refute),
           (q16, Exp, Prove), (q16, Mon, Prove),
           (q17, Exp, Prove), (q17, Mon, Prove)];

fun writeAll () =
  let val file = TextIO.openOut "tests/qbf-test.sym"
      fun oup s = TextIO.output (file, s)
  in oup "%log timers : highlevel.\n";
     oup "%log term : highlevel.\n";
     oup "%log counters : highlevel.\n";
     oup "\n";
     Qbf.writeAll file all;
     TextIO.closeOut file
  end

end

end
