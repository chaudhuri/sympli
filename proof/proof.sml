(* Proof terms *)

structure Proof :> PROOF =
struct

type var = Var.var

type 'a abs = var * 'a
type 'a abs2 = (var * var) * 'a

(* inferable terms *)
datatype inf = Var of var               (* I  ::=  v                      *)
             | App of inf * chk         (*      |  I C                    *)
             | Fst of inf | Snd of inf  (*      |  fst I  |  snd I        *)
             | Chk of chk               (*      |  [C]                    *)

(* checkable terms *)
     and chk = Inf of inf               (* C  ::=  I                      *)
             | Tensor of chk * chk      (*      |  C1 * C2                *)
             | LetTens of inf * chk abs2
                                        (*      |  let u * v = I in C end *)
             | One                      (*      |  1                      *)
             | LetOne of inf * chk      (*      |  let 1 = I in C end     *)
             | Lam of chk abs           (*      |  \v. C                  *)
             | Pair of chk * chk        (*      |  (C1, C2)               *)
             | Unit                     (*      |  ( )                    *)
             | Inl of chk | Inr of chk  (*      |  inl C  |  inr C        *)
             | Case of inf              (*      |  case I of              *)
                       * chk abs        (*           inl u => C           *)
                       * chk abs        (*         | inr u => C           *)
             | Abort of inf             (*      |  abort I                *)
             | Bang of chk              (*      |  ! C                    *)
             | LetBang of inf * chk abs (*      |  let !u = I in C end    *)

             | Bra of chk               (*      |  {C}                    *)
             | LetBra of inf * chk abs  (*      |  let {u} = I in C end   *)

             | Let of inf * chk abs     (*      |  let u = I in C end     *)
             | Ulet of inf * chk abs    (*      |  ulet w = I in C end    *)


exception Check
exception Infer

datatype 'a zone = Dot                        (* Z ::= .        *)
                 | Adj of 'a zone * var * 'a  (*     | Z, v:P   *)

(* 
 * find (., x1:P1, ..., xk:Pk, ..., xn:Pn) v = Pk
 *   note: xk+1, xk+2, ..., xn != xk
 *)
fun find Dot v = NONE
  | find (Adj (Z, u, a)) v = if Var.eq (u, v) then SOME a else find Z v

(* 
 * linearize (., x1:P1, x2:P2, ..., xn:Pn) =
 *    [(x1, P1), (x2, P2), ..., (xn, Pn)]
 *)
fun linearize Z =
    let
      fun lin Dot L = L
        | lin (Adj (Z, u, a)) L = lin Z ((u, a) :: L)
    in
      lin Z []
    end

structure Pr = Prop
type lin = (Lit.skel * bool) zone
type unr = Lit.skel zone


(* 
 * sub_lin (D1, D2) = D1 \subset D2
 * 
 *    for every v in dom(D1), if v :^ P \in D1 then v :^ P \in D2
 *
 *    precondition: dom(D1) = dom(D2)
 *)
fun sub_lin (Dot, Dot) = true
  | sub_lin (Adj (Z1, u1, (P1, c1)), Adj (Z2, u2, (P2, c2))) = 
      not (c1 andalso not c2)
      andalso sub_lin (Z1, Z2)
  | sub_lin _ = false

(*
 * eq_lin (D1, D2) = D1 = D2
 *
 *    precondition: dom(D1) = dom(D2)
 *)
fun eq_lin (Dot, Dot) = true
  | eq_lin (Adj (Z1, u1, (P1, c1)), Adj (Z2, u2, (P2, c2))) = 
      c1 = c2 andalso sub_lin (Z1, Z2)
  | eq_lin _ = false

(*
 * D1/s1 = D2/s2 ?
 *
 *    precondition: dom(D1) = dom(D2)
 *)
fun slack_consistent (D1, true) (D2, true) = true
  | slack_consistent (D1, false) (D2, true) = sub_lin (D2, D1)
  | slack_consistent (D1, true) (D2, false) = sub_lin (D1, D2)
  | slack_consistent (D1, false) (D2, false) = eq_lin (D1, D2)

(* 
 * intersect (D1, D2)
 * 
 *   for every v in dom (D1),
 *     if v consumed in D1 or v consumed in D2
 *     then v consumed in intersect (D1, D2)
 * 
 *   precondition: dom(D1) = dom(D2)
 *)
fun intersect (Dot, Dot) = Dot
  | intersect (Adj (Z1, u1, (P1, c1)), Adj (Z2, u2, (P2, c2))) =
      Adj (intersect (Z1, Z2), u1, (P1, c1 orelse c2))

(* retreive the last element on the zone stack *)
fun tl_lin (Adj (Z, _, (P, c)) : lin) = (Z, c)


exception NotFound

(* 
 * If    Z |- v : (P, false)
 * Then  consume Z v |- v : (P, true)
 *)
fun consume Dot v = raise NotFound
  | consume (Adj (Z, u, (Q, c))) v =
    if Var.eq (u, v) then
      if not c then (Q, Adj (Z, u, (Q, true)))
      else raise NotFound
    else
      let
        val (P, Z) = consume Z v
      in
        (P, Adj (Z, u, (Q, c)))
      end

type ctx = unr * lin

datatype lit = datatype Lit.lit

(* 
 * Assemble a ctx from a linearized representation.
 * Note: all variables in the input must be unique.
 *)
fun ctx (Gs, Ds) = (List.foldr (fn ((u, a), Z) => Adj (Z, u, a)) Dot Gs,
                    List.foldr (fn ((u, a), Z) => Adj (Z, u, (a, false))) Dot Ds)

(* 
 * check (G, Di) (c, P, lx) = (s, Do)
 * 
 *    G ; Di \ Do |-_s c <== P lx
 *)
fun check (G, D) =
    let
      fun chk (Inf i, P, lx) =
          (case P of
             SOME P =>
               let
                 val (Q, s, D) = infer (G, D) i
               in
                 if Lit.eq_skel (P, Q) then (s, D)
                 else raise Check
               end
           | NONE => raise Check)
        | chk (Tensor (c1, c2), SOME (Pr.Tensor (LIT A, LIT B)), false) =
          let
            val (s1, D) = check (G, D) (c1, SOME (#skel A), false)
            val (s2, D) = check (G, D) (c2, SOME (#skel B), false)
          in
            (s1 orelse s2, D)
          end
        | chk (LetTens (i, ((v1, v2), c)), C, lx) = 
          (case infer (G, D) i of
             (Pr.Tensor (LIT A, LIT B), si, D) =>
                let
                  val D = Adj (D, v1, (#skel A, false))
                  val D = Adj (D, v2, (#skel B, false))
                  val (sc, D) = check (G, D) (c, C, lx)
                  val (D, vcons2) = tl_lin D
                  val (D, vcons1) = tl_lin D
                in
                  if sc orelse (vcons1 andalso vcons2)
                  then (si orelse sc, D)
                  else raise Check
                end
           | _ => raise Check)
        | chk (One, SOME (Pr.One), false) = (false, D)
        | chk (LetOne (i, c), C, lx) = 
          (case infer (G, D) i of
             (Pr.One, si, D) =>
               let
                 val (sc, D) = check (G, D) (c, C, lx)
               in
                 (si orelse sc, D)
               end
           | _ => raise Check)
        | chk (Lam (v, c), SOME (Pr.Limp (LIT A, LIT B)), false) =
          let
            val D = Adj (D, v, (#skel A, false))
            val (s, D) = check (G, D) (c, SOME (#skel B), false)
            val (D', vcons) = tl_lin D
          in
            if s orelse vcons then (s, D')
            else raise Check
          end
        | chk (Pair (c1, c2), SOME (Pr.With (LIT A, LIT B)), false) = 
          let
            val (s1, D1) = check (G, D) (c1, SOME (#skel A), false)
            val (s2, D2) = check (G, D) (c2, SOME (#skel B), false)
          in
            if slack_consistent (D1, s1) (D2, s2)
            then (s1 andalso s2, intersect (D1, D2))
            else raise Check
          end
        | chk (Unit, SOME Pr.Top, false) = (true, D)
        | chk (Inl c, SOME (Pr.Choice (LIT A, B)), false) = check (G, D) (c, SOME (#skel A), false)
        | chk (Inr c, SOME (Pr.Choice (A, LIT B)), false) = check (G, D) (c, SOME (#skel B), false)
        | chk (Case (i, (v1, c1), (v2, c2)), C, lx) = 
          (case infer (G, D) i of
             (Pr.Choice (LIT A, LIT B), si, D) =>
               let
                 val D1 = Adj (D, v1, (#skel A, false))
                 val (s1, D1) = check (G, D1) (c1, C, lx)
                 val (D1', v1cons) = tl_lin D1
                 val D2 = Adj (D, v2, (#skel B, false))
                 val (s2, D2) = check (G, D2) (c2, C, lx)
                 val (D2', v2cons) = tl_lin D2
               in
                 if slack_consistent (D1, s1) (D2, s2)
                    andalso (s1 orelse v1cons)
                    andalso (s2 orelse v2cons)
                 then (s1 andalso s2, intersect (D1', D2'))
                 else raise Check
               end
           | _ => raise Check)
        | chk (Abort i, C, lx) =
          (case infer (G, D) i of
             (Pr.Zero, s, D) => (true, D)
           | _ => raise Check)
        | chk (Bang c, SOME (Pr.Bang (LIT A)), false) =
          let
            val (s, _) = check (G, Dot) (c, SOME (#skel A), false)
          in
            (false, D)
          end
        | chk (LetBang (i, (v, c)), C, lx) = 
          (case infer (G, D) i of
             (Pr.Bang (LIT A), si, D) =>
               let
                 val G = Adj (G, v, #skel A)
                 val (sc, D) = check (G, D) (c, C, lx)
               in
                 (si orelse sc, D)
               end
           | _ => raise Check)
        | chk (Bra c, SOME (Pr.Brace (LIT A)), false) = 
            check (G, D) (c, SOME (#skel A), true)
        | chk (LetBra (i, (v, c)), C, true) = 
          (case infer (G, D) i of
             (Pr.Brace (LIT A), si, D) =>
               let
                 val D = Adj (D, v, (#skel A, false))
                 val (sc, D) = check (G, D) (c, C, true)
               in
                 (si orelse sc, D)
               end
           | _ => raise Check)
        | chk (Let (i, (u, c)), C, lx) = 
          let
            val (A, si, D) = infer (G, D) i
            val D = Adj (D, u, (A, false))
            val (sc, D) = check (G, D) (c, C, lx)
            val (D, ucons) = tl_lin D
          in
            if sc orelse ucons then (si orelse sc, D)
            else raise Check
          end
        | chk (Ulet (i, (w, c)), C, lx) = 
          let
            val (A, _, _) = infer (G, Dot) i
            val G = Adj (G, w, A)
          in
            check (G, D) (c, C, lx)
          end
        | chk (c, C, true) = chk (c, C, false)
        | chk _ = raise Check
    in
      chk
    end

(* 
 * infer (G, Di) i = (P, s, Do)
 * 
 *    G ; Di \ Do |-_s i ==> P
 *)
and infer (G, D) i =
    let
      fun inf (Var v) =
          (let
             val (P, D) = consume D v
           in
             (P, false, D)
           end handle NotFound => (case find G v of
                                     SOME P => (P, false, D)
                                   | NONE => raise Infer))
        | inf (App (i, c)) = 
          (case infer (G, D) i of
             (Pr.Limp (LIT A, LIT B), si, D) =>
               let
                 val (sc, D) = check (G, D) (c, SOME (#skel A), false)
               in
                 (#skel B, si orelse sc, D)
               end
           | _ => raise Infer)
        | inf (Fst i) = 
          (case infer (G, D) i of
             (Pr.With (LIT A, B), s, D) => (#skel A, s, D)
           | _ => raise Infer)
        | inf (Snd i) = 
          (case infer (G, D) i of
             (Pr.With (A, LIT B), s, D) => (#skel B, s, D)
           | _ => raise Infer)
        | inf (Chk c) = raise Infer
    in
      inf i
    end

fun test (ctx, p, A, lx) =
    let
      fun consumed Dot = true
        | consumed (Adj (D, u, (P, c))) = c andalso consumed D

      fun doit (p, A) =
          let
            val (s, D) = check ctx (p, A, lx)
          in
            s
            orelse consumed D
            orelse raise Check
          end
    in
      Timers.time1 Timers.validation doit (p, A)
    end

structure M = Var.Map

infix 1 ##
val rc = Var.center {prefix = "u", name = "renumber"}
fun ` f = f (Var.fresh' rc "1")
fun `` f = f (Var.fresh' rc "1", Var.fresh' rc "2")
fun rr ## (u, v) = M.insert (rr, u, v)

(* 
 * Assume:
 * 
 *    1.  G |- c chk
 *    2.  G' |- rr : G
 *    3.  renc rr c = c'
 * 
 * Then:
 * 
 *    1.  G' |- c' chk
 *)
fun renc rr (Inf i) = Inf (reni rr i)
  | renc rr (Tensor (c1, c2)) = Tensor (renc rr c1, renc rr c2)
  | renc rr (LetTens (i, b2)) = LetTens (reni rr i, renb2 rr b2)
  | renc rr One = One
  | renc rr (LetOne (i, c)) = LetOne (reni rr i, renc rr c)
  | renc rr (Lam b) = Lam (renb rr b)
  | renc rr (Pair (c1, c2)) = Pair (renc rr c1, renc rr c2)
  | renc rr Unit = Unit
  | renc rr (Inl c) = Inl (renc rr c)
  | renc rr (Inr c) = Inr (renc rr c)
  | renc rr (Case (i, b, b')) = Case (reni rr i, renb rr b, renb rr b')
  | renc rr (Abort i) = Abort (reni rr i)
  | renc rr (Bang c) = Bang (renc rr c)
  | renc rr (LetBang (i, b)) = LetBang (reni rr i, renb rr b)
  | renc rr (Bra c) = Bra (renc rr c)
  | renc rr (LetBra (i, b)) = LetBra (reni rr i, renb rr b)
  | renc rr (Let (i, b)) = Let (reni rr i, renb rr b)
  | renc rr (Ulet (i, b)) = Ulet (reni rr i, renb rr b)

(* 
 * Assume:
 * 
 *    1.  G |- i inf
 *    2.  G' |- rr : G
 *    3.  reni rr i = i'
 * 
 * Then:
 * 
 *    1.  G' |- i' inf
 *)
and reni rr (Var u) = Var (Option.getOpt (M.find (rr, u), u))
  | reni rr (App (i, c)) = App (reni rr i, renc rr c)
  | reni rr (Fst i) = Fst (reni rr i)
  | reni rr (Snd i) = Snd (reni rr i)
  | reni rr (Chk c) = Chk (renc rr c)

(* 
 * Assume:
 * 
 *    1.  G, u |- c chk
 *    2.  G' |- rr : G
 *    3.  renb rr (u, c) = (u', c')
 * 
 * Then:
 * 
 *    1.  G', u' |- c' : chk
 *)
and renb rr (u, c) =
    `(fn u' => (u', renc (rr ## (u, u')) c))

(* 
 * Assume:
 * 
 *    1.  G, u, v |- c chk
 *    2.  G' |- rr : G
 *    3.  renb rr ((u, v), c) = ((u', v'), c')
 * 
 * Then:
 * 
 *    1.  G', u', v' |- c' : chk
 *)
and renb2 rr ((u, v), c) =
    ``(fn (u', v') => ((u', v'), renc (rr ## (u, u') ## (v, v')) c))

(* 
 * Assume:
 * 
 *   1.  . |- c chk
 *   2.  renumber c = c'
 * 
 * Then:
 * 
 *   1.  . |- c' chk
 *)
fun renumber c = (Var.reset' rc; renc M.empty c)




(* pretty printing *)


open P.Desc 
fun nb_inf (Var _) = false
  | nb_inf (Chk _) = false
  | nb_inf _ = true

fun nb_chk (Inf i) = nb_inf i
  | nb_chk One = false
  | nb_chk Unit = false
  | nb_chk _ = true

fun bracket n p = if n then [string "(", p, string ")"] else [p]

fun pp_let (lt, dec, bod) =
      hvBox (P.Rel 0, [string lt,
                       break {nsp = 1, offset = 2},
                       dec,
                       space 1,
                       string "in", 
                       break {nsp = 1, offset = 2},
                       bod,
                       space 1,
                       string "end"])


fun pp_inf (Var v) = Var.pp v
  | pp_inf (App (i, c)) = 
      hovBox (P.Rel 2, [pp_inf i, space 1] @ bracket (nb_chk c) (pp_chk c))
  | pp_inf (Fst i) =
      hovBox (P.Rel 2, [string "fst", space 1] @ bracket (nb_inf i) (pp_inf i))
  | pp_inf (Snd i) =
      hovBox (P.Rel 2, [string "snd", space 1] @ bracket (nb_inf i) (pp_inf i))
  | pp_inf (Chk c) =
      hBox [string "{", pp_chk c, string "}"]

and pp_chk (Inf i) = pp_inf i
  | pp_chk (Tensor (c1, c2)) =
      hovBox (P.Rel 2,
              bracket (nb_chk c1) (pp_chk c1)
              @ [space 1, string "*", space 1]
              @ bracket (nb_chk c2) (pp_chk c2))
  | pp_chk (LetTens (i, ((v1, v2), c))) = 
      pp_let ("let",
              hvBox (P.Rel 2, [Var.pp v1, string " * ", Var.pp v2, string " =", space 1, pp_inf i]),
              pp_chk c)
  | pp_chk One = string "1"
  | pp_chk (LetOne (i, c)) = 
      pp_let ("let",
              hvBox (P.Rel 2, [string "1 =", space 1, pp_inf i]),
              pp_chk c)
  | pp_chk (Lam (v, c)) = 
      hvBox (P.Rel 0, [string "\\", Var.pp v, string ".", space 1, pp_chk c])
  | pp_chk (Pair (c1, c2)) = 
      hBox [string "(", hvBox (P.Rel 0, [pp_chk c1, string ",", space 1, pp_chk c2]), string ")"]
  | pp_chk Unit = string "()"
  | pp_chk (Inl c) = 
      hovBox (P.Rel 2, [string "inl", space 1] @ bracket (nb_chk c) (pp_chk c))
  | pp_chk (Inr c) = 
      hovBox (P.Rel 2, [string "inr", space 1] @ bracket (nb_chk c) (pp_chk c))
  | pp_chk (Case (i, (v1, c1), (v2, c2))) = 
    let
      fun is_case (Case _) = true
        | is_case _ = false
    in
      hvBox (P.Rel 0, [hvBox (P.Rel 2, [string "case", space 1, pp_inf i, space 1, string "of"]),
                       break {nsp = 1, offset = 2},
                       hvBox (P.Rel 2, [hBox [string "inl", space 1, Var.pp v1, space 1, string "=> "],
                                        cut] @ bracket (is_case c1) (pp_chk c1)),
                       break {nsp = 1, offset = 0},
                       hvBox (P.Rel 2, [hBox [string "| inr", space 1, Var.pp v2, space 1, string "=> "],
                                        cut] @ bracket (is_case c2) (pp_chk c2))])
    end
  | pp_chk (Abort i) = 
      hovBox (P.Rel 2, [string "abort", space 1] @ bracket (nb_inf i) (pp_inf i))
  | pp_chk (Bang c) = 
      hovBox (P.Rel 2, string "!" :: bracket (nb_chk c) (pp_chk c))
  | pp_chk (LetBang (i, (v, c))) = 
      pp_let ("let",
              hvBox (P.Rel 2, [string "!", Var.pp v, string " =", space 1, pp_inf i]),
              pp_chk c)
  | pp_chk (Bra c) = hBox [string "{", pp_chk c, string "}"]
  | pp_chk (LetBra (i, (v, c))) = 
      pp_let ("let",
              hvBox (P.Rel 2, [string "{", Var.pp v, string "} =", space 1, pp_inf i]),
              pp_chk c)
  | pp_chk (Let (i, (v, c))) = 
      pp_let ("let",
              hvBox (P.Rel 2, [Var.pp v, string " =", space 1, pp_inf i]),
              pp_chk c)
  | pp_chk (Ulet (i, (v, c))) = 
      pp_let ("ulet",
              hvBox (P.Rel 2, [Var.pp v, string " =", space 1, pp_inf i]),
              pp_chk c)


fun pp_zone P Z =
      hovBox (P.Rel 2,
              P.delimit
                [string ", "]
                (fn (u, a) => hBox [Var.pp u, string ":", P a])
                (linearize Z))

val pp_unr = pp_zone (Lit.pp_skel 2)
val pp_lin = pp_zone (fn (k, c) => hBox [Lit.pp_skel 2 k,
                                         string "/",
                                         if c then string "1" else string "0"])

fun pp_ctx (G, D) = hBox [pp_unr G, string " ; ", pp_lin D]

end
