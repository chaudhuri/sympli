(* Proof normalization *)
(* Author: Frank Pfenning *)
(* Created: Sat Jun  5 19:32:00 2004 *)

structure DirectNorm :> NORM =
struct

structure P = Proof

(* Notation

   u,v,x,y stand for variables

   c stand for checkable terms (see prop.sml)
   i stand for inferable terms (see prop.sml)
   n stands for normal terms (checkable, no embedded redex)
   r stands for atomic terms (inferable, no embedded redex)
   m stands for definite terms (normal, and not let-form, case, or abort)

   t stand for terms (c, i, n, r, m)
   u.t stands for the abstraction of variable u over term t
   FV(t) stand for the free variables of t
   FV(u.t) = FV(t) - {u}
   s =alpha= t means s is alpha-convertible to t
   s == t means s is alpha/beta/comm-convertible to t
   For remark on commuting conversions see function "commute" below
*)

(* member (x, ys) = true iff variable x is a member of ys *)
fun member (x, ys) =
    let fun m nil = false
          | m (y::ys) = Var.eq(x,y) orelse m ys
    in m ys end

(* genfresh (xs) = x where x does not occur in xs *)
fun gen_fresh (xs) =
    let
      val x = Var.fresh "z"
    in
      if member (x, xs)
	then gen_fresh (xs)
      else x
    end

(* subst (xs, i, x, c) = [i/x]c, where substitution is capture-avoiding
   Invariant: xs contains FV(i)
*)
fun subst (xs, i0, x0, c0) =
    let
      fun ri (P.Var(u)) =
	  (if Var.eq(x0,u) then i0 else P.Var(u))
	| ri (P.App(i,c)) = P.App (ri i, rc c)
        | ri (P.Fst(i)) = P.Fst(ri i)
        | ri (P.Snd(i)) = P.Snd(ri i)
        | ri (P.Chk(c)) = P.Chk(rc c)
      and rc (P.Inf(i)) = P.Inf(ri i)
	| rc (P.Tensor(c1,c2)) = P.Tensor(rc c1, rc c2)
	| rc (P.LetTens(i, ((u1,u2),c))) =
            P.LetTens (ri i, rb2 ((u1,u2),c))
        | rc (P.One) = P.One
        | rc (P.LetOne(i,c)) = P.LetOne (ri i, rc c)
        | rc (P.Lam(u,c)) = P.Lam (rb (u, c))
        | rc (P.Pair(c1,c2)) = P.Pair(rc c1, rc c2)
        | rc (P.Unit) = P.Unit
        | rc (P.Inl(c)) = P.Inl (rc c)
        | rc (P.Inr(c)) = P.Inr (rc c)
        | rc (P.Case(i,(u1,c1),(u2,c2))) =
            P.Case (ri i, rb (u1,c1), rb (u2,c2))
	| rc (P.Abort(i)) = P.Abort(ri i)
	| rc (P.Bang(c)) = P.Bang(rc c)
	| rc (P.LetBang(i, b)) =
            P.LetBang(ri i, rb b)
        | rc (P.Bra(c)) = P.Bra(rc c)
        | rc (P.LetBra(i, b)) = 
            P.LetBra(ri i, rb b)
        | rc (P.Let(i,b)) = P.Let(ri i, rb b)
	| rc (P.Ulet(i,b)) = P.Let(ri i, rb b)
      and rb (u,c) =
	  (if Var.eq(x0,u) then (u,c)
	   else let val (u,c) = if member(u,xs) then fc (xs,(u,c)) else (u,c)
		in (u, rc c) end)
      and rb2 ((u1, u2), c) = (* u1 <> u2 *)
	  (if Var.eq(x0,u1) orelse Var.eq(x0,u2)
	     then ((u1,u2), c)
	   else let
		  val (u1, c) = if member(u1,xs) then fc(u2::xs, (u1,c)) else (u1,c)
		  val (u2, c) = if member(u2,xs) then fc(u1::xs, (u2,c)) else (u2,c)
		in
		  ((u1,u2), rc c)
		end)
      and fc (xs, (u,c)) =
	  let
	     val u' = gen_fresh (xs)
	  in
	    (u', subst (u'::nil, P.Var(u'), u, c))
	  end
    in
      rc c0
    end

(* substc (xs, c1, u, c2) = [c1/u]c2, where substitution is capture-avoiding
   Invariant: xs contains all free variables in c1
*)
fun substc (xs, c1, u, c2) =
      subst (xs, P.Chk(c1), u, c2) 

(* freshen (xs, (u,c)) = (u',c'), where u.c =alpha= u'.c' and u' not in xs
   Invariant: xs contains FV(u.c)
   Always renames
*)
fun freshen (xs, (u,c)) =
    let
      val u' = gen_fresh (xs)
      (* val _ = checkFresh (u', xs) *)
    in
      (u', subst(u'::nil, P.Var(u'), u, c))
    end

(* stdize (xs, (u,c)) = (u',c'), where u.c =alpha= u'.c' and u' not in xs
   Invariant: xs contains FV(u.c)
   Renames only if necessary
*)
fun stdize (xs, (u,c)) =
    if member(u,xs) then freshen (xs, (u,c)) else (u,c)

(* stdize2 (xs, ((u1,u2),c)) = ((u1',u2'),c'), where u1.u2.c =alpha= u1'.u2'.c'
   and u1', u2' not in xs
   Invariant: xs contains FV(u1.u2.c), u1 <> u2
   Renames only if necessary
*)
fun stdize2 (xs, ((u1,u2),c)) =
    let
      val (u1,c) = if member(u1,xs) then freshen (u2::xs, (u1,c)) else (u1,c)
      val (u2,c) = if member(u2,xs) then freshen (u1::xs, (u2,c)) else (u2,c)
    in 
      ((u1,u2),c)
    end

(* normi (xs, i) = n
   normc (xs, c) = n
   normb (xs, (u,c)) = (v,n)
   where i == n, c == n, u.c == v.n (and n is normal)
   (s == t means alpha, beta, and commuting conversions)
   Invariant: xs contains FV(i), FV(c), FV(u.c), respectively
*)
fun normi (xs, P.Var(u)) = P.Inf (P.Var(u))
  | normi (xs, P.App(i,c)) = commute (APP c) (xs, normi(xs,i))
  | normi (xs, P.Fst(i)) = commute FST (xs, normi(xs,i))
  | normi (xs, P.Snd(i)) = commute SND (xs, normi(xs,i))
  | normi (xs, P.Chk(c)) = normc (xs, c)
and normc (xs, P.Inf(i)) = normi (xs, i)
  | normc (xs, P.Tensor(c1,c2)) = P.Tensor (normc (xs,c1), normc (xs, c2))
  | normc (xs, P.LetTens(i,b2)) =
      commute (LETTENS b2) (xs, normi (xs,i))
  | normc (xs, P.One) = P.One
  | normc (xs, P.LetOne(i,c)) =
      commute (LETONE c) (xs, normi (xs,i))
  | normc (xs, P.Lam(u,c)) = P.Lam (normb (xs,(u,c)))
  | normc (xs, P.Pair(c1,c2)) = P.Pair (normc (xs, c1), normc (xs, c2))
  | normc (xs, P.Unit) = P.Unit
  | normc (xs, P.Inl(c)) = P.Inl (normc (xs, c))
  | normc (xs, P.Inr(c)) = P.Inr (normc (xs, c))
  | normc (xs, P.Case(i, (u1, c1), (u2, c2))) =
      commute (CASE (u1, c1) (u2, c2)) (xs, normi (xs, i))
  | normc (xs, P.Abort(i)) =
      commute ABORT (xs, normi (xs, i))
  | normc (xs, P.Bang(c)) = P.Bang (normc (xs, c))
  | normc (xs, P.LetBang(i,b)) =
      commute (LETBANG b) (xs, normi (xs, i))
  | normc (xs, P.Bra(c)) = P.Bra (normc (xs, c))
  | normc (xs, P.LetBra(i, b)) = 
      commute (LETBRA b) (xs, normi (xs, i))
  | normc (xs, P.Let(i,b)) =
      commute (LET b) (xs, normi (xs, i))
  | normc (xs, P.Ulet(i,b)) =
      commute (ULET b) (xs, normi (xs, i))
and normb (xs, (u,c)) =
    let
      val (u,c) = stdize (xs, (u,c))
    in
      (u, normc (u::xs, c))
    end

(* We write m for a normal term that is not a let-form, case, or abort *)
(* n is always a normal term, r always an atomic term *)

(* APP c2 (xs, m) = n and n == m c1, xs contains FV(m) and FV(c2) *)
and APP c2 (xs, P.Lam(u,n1)) = normc (xs, substc (xs, c2, u, n1))
  | APP c2 (xs, P.Inf(r)) = P.Inf(P.App(r, normc (xs, c2)))

(* FST (xs, m) = n and n == fst m, xs contains FV(m) *)
and FST (xs, P.Pair(n1,n2)) = n1
  | FST (xs, P.Inf(r)) = P.Inf(P.Fst(r))

(* SND (xs, m) = n and n == snd m, xs contains FV(m) *)
and SND (xs, P.Pair(n1,n2)) = n2
  | SND (xs, P.Inf(r)) = P.Inf(P.Snd(r))

(* LETTENS ((u1,u2), c) (xs, m) = n and n == (let u1 * u2 = m in c),
   xs contains FV(m) and FV(u1.u2.c)
*)
and LETTENS ((u1,u2), c) (xs, P.Tensor(n1,n2)) =
      normc (xs, substc (xs, n1, u1, substc (xs, n2, u2, c)))
  | LETTENS ((u1,u2), c) (xs, P.Inf(r)) =
    let
      val ((u1,u2),c) = stdize2 (xs, ((u1,u2),c))
    in
	P.LetTens (r, ((u1, u2), normc (u1::u2::xs, c)))
    end

(* LETONE c (xs, m) = n and n == (let 1 = m in c),
   xs contains FV(m) and FV(c)
*)
and LETONE c (xs, P.One) = normc (xs, c)
  | LETONE c (xs, P.Inf(r)) = P.LetOne (r, normc (xs, c))

(* CASE (u1,c1) (u2,c2) (xs, m) = n and n == (case m of u1 => c1 | u2 => c2),
   xs contains FV(m), FV(u1.c1), and FV(u2.c2) *)
and CASE (u1,c1) (u2,c2) (xs, P.Inl(n)) = normc (xs, substc (xs, n, u1, c1))
  | CASE (u1,c1) (u2,c2) (xs, P.Inr(n)) = normc (xs, substc (xs, n, u2, c2))
  | CASE (u1,c1) (u2,c2) (xs, P.Inf(r)) = P.Case(r, normb(xs, (u1,c1)), normb(xs, (u2,c2)))

(* ABORT (xs, m) = n and n == abort m, xs contains FV(m) *)
and ABORT (xs, P.Inf(r)) = P.Abort(r)

(* LETBANG (u,c) (xs, m) = n and n == (let !u = m in c),
   xs contains FV(m) and FV(u.c)
*)
and LETBANG (u,c) (xs, P.Bang(n)) = normc (xs, substc (xs, n, u, c))
  | LETBANG (u,c) (xs, P.Inf(r)) = P.LetBang (r, normb (xs, (u, c)))

(* LETBRA (u,c) (xs, m) = n and n == (let !u = m in c),
   xs contains FV(m) and FV(u.c)
*)
and LETBRA (u,c) (xs, P.Bra(n)) =
    let
      fun lsub (P.LetBra(n, (v, n'))) = P.LetBra(n, (v, lsub n'))
        | lsub n = normc(xs, substc(xs, n, u, c))
    in
      lsub n
    end
  | LETBRA (u,c) (xs, P.Inf(r)) = P.LetBra (r, normb (xs, (u, c)))

(* LET (u,c) (xs, m) = n and n == (let u = m in c),
   xs contains FV(m) and FV(u.c)
*)
and LET (u,c) (xs, P.Inf(r)) = P.Let (r, normb (xs, (u, c)))
  | LET (u,c) (xs, n) = normc (xs, substc (xs, n, u, c))

(* ULET (u,c) (xs, m) = n and n == (ulet u = m in c),
   xs contains FV(m) and FV(u.c)
*)
and ULET (u,c) (xs, P.Inf(r)) = P.Ulet (r, normb (xs, (u,c)))
  | ULET (u,c) (xs, n) = normc (xs, substc (xs, n, u, c))

(* 
   Commuting Contexts
   f ::= let*(r,u1.u2.f) | let1(r,f)
       | case(r,u1.f1,u2.f2) | abort(r)
       | let!(r,u.f) | let(r,u.f) | ulet(r,u.f)
       | []

   Elimination Forms
   F(_) ::= app(_,c) | fst(_) | snd(_)
          | let*(_,u1.u2.c) | let1(_,c)
          | case(_,u1.f1,u2.f2) | abort(_)
          | let!(_,u.f) | let(_,u.f) | ulet(_,u.f)

   Note that every normal term n has the form f where all
   holes are filled with m's, f[m1,...,mk].  Each mj may
   make sense in a different variable context xsj, since
   commuting contexts bind variables.

   The commuting conversions are F(f[m1,...,mk]) = f[F(m1),...,F(mk)]
   where F is an elimination form.  More precisely, accounting
   for the variables bound in f:

   commute F (xs, n) = n' where n' == F (xs, n), xs contains FV(n)

   This is implemented as follows:
   If n = f[m1,...,mk] then F(xs, N) = f[F(xs1,m1),...,F(xsk,mk)]
   where each xsj contains FV(mj).
*)
and commute F (xs, P.LetTens(r,((u1,u2),n))) =
    let
      val ((u1,u2), n) = stdize2 (xs, ((u1,u2), n))
    in
      P.LetTens (r, ((u1,u2), commute F (u1::u2::xs, n)))
    end
  | commute F (xs, P.LetOne(r,n)) =
      P.LetOne (r, commute F (xs, n))
  | commute F (xs, P.Case(r, (u1,n1), (u2,n2))) =
    let
      val (u1,n1) = stdize(xs, (u1, n1))
      and (u2,n2) = stdize(xs, (u2, n2))
    in
      P.Case (r, (u1, commute F (u1::xs, n1)), (u2, commute F (u2::xs, n2)))
    end
  | commute F (xs, P.Abort(r)) =
      P.Abort(r)
  | commute F (xs, P.LetBang(r, (u, n))) =
    let
      val (u,n) = stdize (xs, (u,n))
    in
      P.LetBang (r, (u, commute F (u::xs, n)))
    end
  | commute F (xs, P.LetBra(r, (u, n))) =
    let
      val (u,n) = stdize (xs, (u,n))
    in
      P.LetBra (r, (u, commute F (u::xs, n)))
    end
  | commute F (xs, P.Let(r, (u, n))) =
    let
      val (u,n) = stdize (xs, (u, n))
    in
      P.Let (r, (u, commute F (u::xs, n)))
    end
  | commute F (xs, P.Ulet(r, (u, n))) =
    let
      val (u, n) = stdize (xs, (u, n))
    in
      P.Ulet (r, (u, commute F (u::xs, n)))
    end
  | commute F (xs, n) = (* here n must be an m *)
    F (xs, n)

(* cnorm c = n where c == n
   Invariant: c closed
*)
fun cnorm c = normc (nil, c)

end;
