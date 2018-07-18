(* 
 * Proof normalization
 * Author: Kaustuv Chaudhuri
 *)

functor FoldNormFn (structure Fold : FOLD_HEUR)
        :> NORM =
struct

open P.Desc

(* Continue with fresh variables *)
fun ` f = f (Var.fresh "1")
fun `` f = f (Var.fresh "1", Var.fresh "2")

open Proof
structure M = Var.Map

(* 
 * Conventions:
 * 
 *    i, c, r, n, t   ... meta variables for inferable, checkable, 
 *                        reduced, normal, and all proof terms
 * 
 *    t1 == t2        ... t1 is alpha-beta-gamma equivalent to t2
 *
 *    e `--> e'       ... (SML) expression (represented as) e
 *                           evaluates to (SML) expression e'
 *)


(* 
 *    D  |- ss : G        ... like the usual except variables in dom(G) but not
 *                             in ss are self-bound:
 *
 * 
 *                    D |- ss : G    D |- n  norm
 * ------------      -----------------------------
 *  D |- . : .            D |- ss, n/u : G, u
 * 
 *  D, u |- ss : G    u not in dom(ss)
 * ------------------------------------
 *          D, u |- ss : G, u
 *
 *
 * Some standard judgements:
 *
 *    G |- c  chk         ... c is a well-formed checkable term in G
 *    G |- i  inf         ... i is a well-formed inferable term in G
 *
 *    D |- n  norm        ... n is a well-formed normal term in G
 *    D |- r  red         ... r is a well-formed reduced term in G
 *
 * Also we have:
 *
 *    G |- n  norm#       ... BV(n) intersect G = {} and G |- n  norm
 *    G |- r  red#        ... BV(r) intersect G = {} and G |- r red
 *
 *    G' |- rr :# G       ... rr is a renaming substitution, i.e.,
 *                               G intersect G' = {}
 *)

(* G |- dot : G *)
val dot = M.empty

(* 
 * Assume:
 *
 *   1. D |- ss : G
 *   2. lookup ss v `--> n
 *
 * Then:
 *
 *   1. D |- n norm
 *   2. n = ss(v) if v in dom(ss)
 *      n = v     if v not in dom(ss)
 *)
fun lookup ss v = Option.getOpt (M.find (ss, v), Inf (Var v))

infix 1 ++ ##

(* 
 * bind n to u in ss
 * 
 * Assume:
 * 
 *   1. D |- ss : G
 *   2. D |- n norm
 *   3. ss ++ (u, n) `--> ss'
 * 
 * Then:
 * 
 *   1. D |- ss' : G + u
 *   2. ss' (u) = n
 *      ss' (v) = ss(v)  if v in G - u
 *)
fun ss ++ (u, n) = M.insert (ss, u, n)

(* 
 * bind n to v in ss
 * 
 * Assume:
 * 
 *   1. D |- ss : G
 *   2. ss ++ (u, v) `--> ss'
 * 
 * Then:
 * 
 *   1. D |- ss' : G + u
 *   2. ss' (u) = v
 *      ss' (u') = ss(u')  if u' in G - u
 *)
fun ss ## (u,v) = ss ++ (u, Inf (Var v))

(* 
 * Assume:
 * 
 *   1.  G' |- rr :# G
 *   2.  G |- n  norm
 *   3.  renn rr n `--> n'
 * 
 * Then:
 * 
 *   1.  G' |- n'  norm#
 *
 * Similarly for reni, renb and renb2
 *)
fun renn rr (Inf r) = Inf (renr rr r)
  | renn rr (Tensor (n1, n2)) = Tensor (renn rr n1, renn rr n2)
  | renn rr (LetTens (r, b2)) =
      LetTens (renr rr r, renb2 rr b2)
  | renn rr One = One
  | renn rr (LetOne (r, n)) = LetOne (renr rr r, renn rr n)
  | renn rr (Lam b) = Lam (renb rr b)
  | renn rr (Pair (n1, n2)) = Pair (renn rr n1, renn rr n2)
  | renn rr Unit = Unit
  | renn rr (Inl n) = Inl (renn rr n)
  | renn rr (Inr n) = Inr (renn rr n)
  | renn rr (Case (r, b1, b2)) =
      Case (renr rr r, renb rr b1, renb rr b2)
  | renn rr (Abort r) = Abort (renr rr r)
  | renn rr (Bang n) = Bang (renn rr n)
  | renn rr (LetBang (r, b)) = LetBang (renr rr r, renb rr b)
  | renn rr (Bra n) = Bra (renn rr n)
  | renn rr (LetBra (r, b)) = LetBra (renr rr r, renb rr b)
  | renn rr (Let (r, b)) = Let (renr rr r, renb rr b)
  | renn rr (Ulet (r, b)) = Ulet (renr rr r, renb rr b)
and renr rr (Var v) = Var (Option.getOpt (M.find (rr, v), v))
  | renr rr (App (r, n)) = App (renr rr r, renn rr n)
  | renr rr (Fst r) = Fst (renr rr r)
  | renr rr (Snd r) = Snd (renr rr r)
and renb rr (u, n) = `(fn v => (v, renn (rr ++ (u, v)) n))
and renb2 rr ((u1, u2), n) =
      ``(fn (v1, v2) => ((v1, v2), renn (rr ++ (u1, v1) ++ (u2, v2)) n))

(* 
 * Assume:
 * 
 *   1.  G |- n  norm
 *   2.  sharpen n `--> n'
 * 
 * Then:
 * 
 *   1.  G |- n'  norm#
 *)
fun sharpen n = renn dot n

(* 
 * Define commuting frame:
 *
 *  f  ::=  let u * v = r in [] end
 *       |  let 1 = r in [] end
 *       |  case r of inl u => [] | inr v => []
 *       |  abort r
 *       |  let ! u = r in [] end
 *       |  let u = r in [] end
 *       |  ulet u = r in [] end
 *
 * Let f.i represent the ith hole in f. The variables in f that are
 * in scope at f.i define a context G, written as:
 *
 *             f.i |> G
 *
 * Observe that if  G |- f [n1, n2, ..., nk]  norm#, and  f.i |> Gi, then
 * G, Gi |- ni norm#.
 *
 * Assume:
 *
 *     1.  G |- f [n1, n2, ..., nk]  norm#
 *     2.  f.i |> Gi
 *     3.  F ni `--> ni'
 *     4.  G, Gi |- ni' norm
 *     5.  ni' == ni
 *
 * Then:
 *
 *     1.  commute F (f [n1, n2, ..., nk]) = f [n1', n2', ..., nk']
 *     2.  f [n1', n2', ..., nk']  ==  f [n1, n2, ..., nk]
 *     3.  G |- f [n1', n2', ..., nk']  norm
 *)
fun commute F (LetTens (r, (uv, n))) = LetTens (r, (uv, F n))
  | commute F (LetOne (r, n)) = LetOne (r, F n)
  | commute F (Case (r, (u1, n1), (u2, n2))) = 
      Case (r, (u1, F n1), (u2, F n2))
  | commute F (Abort r) = Abort r
  | commute F (LetBang (r, (u, n))) = LetBang (r, (u, F n))
  | commute F (LetBra (r, (u, n))) = LetBra (r, (u, F n))
  | commute F (Let (r, (u, n))) = Let (r, (u, F n))
  | commute F (Ulet (r, (u, n))) = Ulet (r, (u, F n))

(* 
 * Assume:
 * 
 *   1.  G |- i  inf
 *   2.  D |- ss : G
 *   3.  normi ss i `--> n
 * 
 * Then:
 * 
 *   1.  D |- n  norm
 *   2.  n == i[ss]
 *)
fun normi ss (Var v) = lookup ss v
  | normi ss (App (i, c)) = APP (sharpen (normi ss i), normc ss c)
  | normi ss (Fst i) = FST (sharpen (normi ss i))
  | normi ss (Snd i) = SND (sharpen (normi ss i))
  | normi ss (Chk c) = normc ss c

(* 
 * Assume:
 * 
 *   1.  D |- n1  norm#
 *   2.  D |- n2  norm
 *   4.  APP (n1, n2) `--> n
 * 
 * Then:
 * 
 *   1.  D |- n  norm
 *   2.  n == [n1] n2
 *)
and APP (Lam (u, n1), n2) = normc (dot ++ (u, n2)) n1
  | APP (Inf r1, n2) = Inf (App (r1, n2))
  | APP (n1, n2) = commute (fn n1 => APP (n1, n2)) n1

(* 
 * Assume:
 * 
 *   1.  G |- n  norm#
 *   2.  FST n `--> n'
 * 
 * Then:
 * 
 *   1.  G |- n'  norm
 *   2.  n' == fst [n]
 *
 * Similarly for SND
 *)
and FST (Pair (n1, n2)) = n1
  | FST (Inf r) = Inf (Fst r)
  | FST n = commute FST n

and SND (Pair (n1, n2)) = n2
  | SND (Inf r) = Inf (Snd r)
  | SND n = commute SND n

(* 
 * Assume:
 * 
 *   1.  G |- c  chk
 *   2.  D |- ss : G
 *   3.  normc ss c `--> n
 * 
 * THen:
 * 
 *   1.  D |- n  norm
 *   2.  n == c[ss]
 *)
and normc ss (Inf i) = normi ss i
  | normc ss (Tensor (c, c')) = Tensor (normc ss c, normc ss c')
  | normc ss (LetTens (i, ((u, v), c))) =
      LET_TENS ss (u, v, sharpen (normi ss i), c)
  | normc ss One = One
  | normc ss (LetOne (i, c)) =
      LET_ONE ss (sharpen (normi ss i), c)
  | normc ss (Lam (u, c)) =
      `(fn v => Lam (v, normc (ss ## (u,v)) c))
  | normc ss (Pair (c, c')) = Pair (normc ss c, normc ss c')
  | normc ss Unit = Unit
  | normc ss (Inl c) = Inl (normc ss c)
  | normc ss (Inr c) = Inr (normc ss c)
  | normc ss (Case (i, b1, b2)) =
      CASE (ss, ss) (sharpen (normi ss i), b1, b2)
  | normc ss (Abort i) = ABORT (sharpen (normi ss i))
  | normc ss (Bang c) = Bang (normc ss c)
  | normc ss (LetBang (i, (u, c))) = 
      LET_BANG ss (u, sharpen (normi ss i), c)
  | normc ss (Bra c) = Bra (normc ss c)
  | normc ss (LetBra (i, (u, c))) = 
      LET_BRA ss (u, sharpen (normi ss i), c)
  | normc ss (Let (i, (u, c))) =
      LET Let ss (u, normi ss i, c)
  | normc ss (Ulet (i, (u, c))) =
      LET Ulet ss (u, normi ss i, c)

(* 
 * Assume:
 * 
 *   1.  D |- n  norm#
 *   2.  G, u, v |- c  chk
 *   3.  D |- ss : G
 *   4.  LET_TENS ss (u, v, n, c) `--> n'
 * 
 * Then:
 * 
 *   1.  D |- n'  norm
 *   2.  n' == let u * v = [n] in c[ss] end
 *)
and LET_TENS ss (u, v, Tensor (n1, n2), c) =
      normc (ss ++ (u, n1) ++ (v, n2)) c
  | LET_TENS ss (u, v, Inf r, c) = 
      LetTens (r, ``(fn (u', v') =>
                        ((u',v'), normc (ss ## (u, u') ## (v, v')) c)))
  | LET_TENS ss (u, v, n, c) =
      commute (fn n => LET_TENS ss (u, v, n, c)) n

(* 
 * Assume:
 * 
 *   1.  D |- n  norm#
 *   2.  G |- c  chk
 *   3.  D |- ss : G
 *   4.  LET_ONE ss (n, c) `--> n'
 * 
 * Then:
 * 
 *   1.  D |- n'  norm
 *   3.  n' == let 1 = [n] in c[ss] end
 *)
and LET_ONE ss (One, c) = normc ss c
  | LET_ONE ss (Inf r, c) = LetOne (r, normc ss c)
  | LET_ONE ss (n, c) = commute (fn n => LET_ONE ss (n, c)) n

(* 
 * Assume:
 * 
 *   1.  D |- n  norm#
 *   2.  G1, u1 |- c1  chk
 *   3.  G2, u2 |- c2  chk
 *   4.  D |- ss1 : G1
 *   5.  D |- ss2 : G2
 *   6.  CASE (ss1, ss2) (n, (u1, c1), (u2, c2)) `--> n'
 * 
 * Then:
 * 
 *   1.  D |- n'  norm
 *   2.  n' == case [n] of inl u1 => c1[ss1] | inr u2 => c2[ss2]
 *)
and CASE (ss1, ss2) (Inl n, (u, c), _) =
      normc (ss1 ++ (u, n)) c
  | CASE (ss1, ss2) (Inr n, _, (u, c)) =
      normc (ss2 ++ (u, n)) c
  | CASE (ss1, ss2) (Inf r, (u1, c1), (u2, c2)) = 
      Case (r,
            `(fn v1 => (v1, normc (ss1 ## (u1, v1)) c1)),
            `(fn v2 => (v2, normc (ss2 ## (u2, v2)) c2)))
  | CASE (ss1, ss2) (n, (u1, c1), (u2, c2)) = 
      commute (fn n => CASE (ss1, ss2) (n, (u1, c1), (u2, c2))) n

(* 
 * Assume:
 * 
 *   1.  D |- n  norm#
 *   2.  ABORT n `--> n'
 * 
 * Then:
 * 
 *   1.  D |- n'  norm
 *   2.  n' == abort [n]
 *)
and ABORT (Inf r) = Abort r
  | ABORT n = commute ABORT n


(* 
 * Assume:
 * 
 *   1.  D |- n  norm#
 *   2.  G, u |- c  chk
 *   3.  D |- ss : G
 *   4.  LET_BANG ss (u, n, c) `--> n'
 * 
 * Then:
 * 
 *   1.  D |- n'  norm
 *   2.  n' == let !u = [n] in c[ss] end
 *)
and LET_BANG ss (u, Bang n, c) = normc (ss ++ (u, n)) c
  | LET_BANG ss (u, Inf r, c) =
      LetBang (r, `(fn u' => (u', normc (ss ## (u, u')) c)))
  | LET_BANG ss (u, n, c) = 
      commute (fn n => LET_BANG ss (u, n, c)) n

(* 
 * Assume:
 * 
 *   1.  D |- n  norm#
 *   2.  G, u |- c  chk
 *   3.  D |- ss : G
 *   4.  LET_BRA ss (u, n, c) `--> n'
 * 
 * Then:
 * 
 *   1.  D |- n'  norm
 *   2.  n' == let {u} = [n] in c[ss] end
 *)
and LET_BRA ss (u, Bra n, c) =
    let
      fun lsub (LetBra (n, (v, n'))) = LetBra (n, (v, lsub n'))
        | lsub n = normc (ss ++ (u, n)) c
    in
      lsub n
    end
  | LET_BRA ss (u, Inf r, c) =
      LetBra (r, `(fn u' => (u', normc (ss ## (u, u')) c)))
  | LET_BRA ss (u, n, c) = 
      commute (fn n => LET_BRA ss (u, n, c)) n

(* 
 * Assume:
 * 
 *   1.  D |- n  norm
 *   2.  G, u |- c  chk
 *   3.  D |- ss : G
 *   4.  LET lt ss (u', n, c) `--> n'
 * 
 * Then:
 * 
 *   1.  D |- n'  norm
 *   2.  n' == lt u = [n] in c[ss] end
 *)
and LET lt ss (u, Inf r, c) = 
      if Fold.fire r then normc (ss ++ (u, Inf r)) c
      else lt (r, `(fn u' => (u', normc (ss ## (u, u')) c)))
  | LET lt ss (u, n, c) = normc (ss ++ (u, n)) c


(* 
 * Assume:
 * 
 *   1.  . |- c  chk
 *   2.  cnorm c `--> n
 * 
 * Then:
 * 
 *   1.  . |- n  norm
 *   2.  n == c
 *)
fun cnorm c = normc dot c

end
