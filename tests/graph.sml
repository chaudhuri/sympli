signature GRAPH =
sig
  
  type node = string
  type edge = node * node
  
  datatype graph = Graph of node list * edge list
  
  datatype oper = Prove | Refute
  
  datatype prob = Hamilton | Euler
  
  val hamilton : graph -> Prop.prop
  val euler : graph -> Prop.prop
  val write : TextIO.outstream -> (graph * prob * oper) -> unit
  val writeAll : TextIO.outstream -> (graph * prob * oper) list -> unit
  
end

structure Graph :> GRAPH =
struct

local open Prop in
  
  type node = string
  type edge = node * node
  
  datatype graph = Graph of (node list * edge list)
  
  datatype oper = Prove | Refute
  
  datatype prob = Hamilton | Euler
  
  fun ` c x = Prop (c x)
     
  fun atom a = `Atomic (Atom.atom a)
  fun atom' a = `Atomic (Atom.atom (a ^ "'"))
  
  fun hamiltonV (v1::vs) = 
    let val init = atom' v1
        fun addV (v, prop) = `Tensor (atom' v, prop)
    in foldl addV init vs
    end
  
  fun hamiltonE (e1::es) =
    let fun edge (v1, v2) = `With (`Limp (`Tensor (atom v1, atom' v2), atom v2), Prop (One))
        val init = edge e1
        fun addE (e, prop) = `Tensor (edge e, prop)
    in foldl addE init es
    end
  
  fun hamilton (Graph (v::vs, e)) =
    `Limp (`Tensor (atom v, `Tensor (hamiltonV (v::vs), hamiltonE e)), atom v)
  
  fun eulerE (e1::es) =
    let fun edge (v1, v2) = `With (`Limp (atom v1, atom v2), `Limp (atom v2, atom v1))
        val init = edge e1
        fun addE (e, prop) = `Tensor (edge e, prop)
    in foldl addE init es
    end
  
  fun euler (Graph (v::vs, e)) = `Limp (`Tensor (atom v, eulerE e), atom v)
  
  fun write stream (g, prob, oper) =
    let val opstr = case oper of Prove => "prove" | Refute => "refute"
        val qprop = case prob of Hamilton => hamilton g | Euler => euler g
        val propstr = P.unparse (Prop.pp_prop qprop)
    in TextIO.output (stream, "%" ^ opstr ^ " " ^ propstr ^ ".\n\n")
    end
  
  fun writeAll stream l = List.app (write stream) l
  
end

end

structure Gs =
struct

local open Graph in

val g0 = Graph (["a", "b", "c"], [("a", "b"), ("b", "c"), ("c", "a")])

val g1 = Graph (["a", "b", "c", "d"], [("a", "b"), ("b", "c"), ("c", "d"), ("d", "a"), ("a", "c")])

val konigsberg = Graph (["a", "b", "c", "d"], [("a", "b"), ("a", "b"), ("a", "c"), ("a", "c"), ("a", "d"), ("c", "d"), ("b", "d")])

val all = [(g0, Hamilton, Prove), (g0, Euler, Prove),
           (g1, Hamilton, Prove), (g1, Euler, Refute),
           (konigsberg, Hamilton, Refute), (konigsberg, Euler, Refute)]

fun writeAll () =
  let val file = TextIO.openOut "tests/graph-test.sym"
      fun oup s = TextIO.output (file, s)
  in oup "%log timers : highlevel.\n";
     oup "%log term : highlevel.\n";
     oup "%log counters : highlevel.\n";
     oup "\n";
     Graph.writeAll file all;
     TextIO.closeOut file
  end

end

end
