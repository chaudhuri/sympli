structure Onf :> ONF =
struct

open Proof
structure Pr = Prop

fun ` f x = Inf (f x)
val $ = Var
val `$ = ` $

fun % f x = Chk (f x)

fun fresh f = f (Var.fresh "fresh1")
fun fresh2 f = f (Var.fresh "fresh2.1", Var.fresh "fresh2.2")
fun fresh3 f = f (Var.fresh "fresh3.1", Var.fresh "fresh3.2", Var.fresh "3.3")

fun norm (Pr.Prop A) =
    let
      fun onf (Pr.Tensor (B, C)) =
          let
            val (B', fB, gB) = norm B
            val (C', fC, gC) = norm C
          in
            fresh3
            (fn (u, v1, v2) =>
                case (B', C') of
                  (_, Pr.One) =>
                  let
                    val A' = B'
                  in
                    (A',
                     %Lam (u, LetTens ($u, ((v1, v2), LetOne (App (fC, `$v2), `App (fB, `$v1))))),
                     %Lam (u, Tensor (`App (gB, `$u), `App (gC, One))))
                  end
                | (Pr.One, _) => 
                  let
                    val A' = C'
                  in
                    (A',
                     %Lam (u, LetTens ($u, ((v1, v2), LetOne (App (fB, `$v1), `App (fC, `$v2))))),
                     %Lam (u, Tensor (`App (gB, One), `App (gC, `$u))))
                  end
                | _ =>
                  let
                    val A' = Pr.Tensor (Pr.Prop B', Pr.Prop C')
                  in
                    (A',
                     %Lam (u, LetTens ($u, ((v1, v2), Tensor (`App (fB, `$v1), `App (fC, `$v2))))),
                     %Lam (u, LetTens ($u, ((v1, v2), Tensor (`App (gB, `$v1), `App (gC, `$v2))))))
                  end)
          end
        | onf (Pr.Limp (B, C)) = 
          let
            val (B', fB, gB) = norm B
            val (C', fC, gC) = norm C
          in
            fresh2
            (fn (u, v) =>
                case B' of
                  Pr.One =>
                  let
                    val A' = C'
                  in
                    (A',
                     %Lam (u, `App (fC, `App ($u, `App (gB, One)))),
                     %Lam (u, Lam (v, LetOne (App (fB, `$v),
                                              `App (gC, `$u)))))
                  end
                | _ => 
                  let
                    val A' = Pr.Limp (Pr.Prop B', Pr.Prop C')
                  in
                    (A',
                     %Lam (u, Lam (v, `App (fC, `App ($u, `App (gB, `$v))))),
                     %Lam (u, Lam (v, `App (gC, `App ($u, `App (fB, `$v))))))
                  end)
          end
        | onf (Pr.With (B, C)) = 
          let
            val (B', fB, gB) = norm B
            val (C', fC, gC) = norm C
          in
            fresh
            (fn u =>
                case (B', C') of
                  (Pr.One, Pr.One) =>
                  let
                    val A' = Pr.One
                  in
                    (A',
                     %Lam (u, `App (fB, `Fst ($u))),
                     %Lam (u, Pair (`App (gB, `$u), `App (gC, One))))
                  end
                | (Pr.One, _) =>         (* rewrite it as C&1 instead of 1&C *)
                  let
                    val A' = Pr.With (Pr.Prop C', Pr.Prop B')
                  in
                    (A',
                     %Lam (u, Pair (`App (fB, `Snd ($u)), `App (fC, `Fst ($u)))),
                     %Lam (u, Pair (`App (gB, `Snd ($u)), `App (gC, `Fst ($u)))))
                  end
                | _ => 
                  let
                    val A' = Pr.With (Pr.Prop B', Pr.Prop C')
                  in
                    (A',
                     %Lam (u, Pair (`App (fB, `Fst ($u)), `App (fC, `Snd ($u)))),
                     %Lam (u, Pair (`App (gB, `Fst ($u)), `App (gC, `Snd ($u)))))
                  end)
          end
        | onf (Pr.Choice (B, C)) = 
          let
            val (B', fB, gB) = norm B
            val (C', fC, gC) = norm C
          in
            fresh3
            (fn (u, v1, v2) =>
                case (B', C') of
                  (Pr.One, Pr.One) =>
                  let
                    val A' = Pr.One
                  in
                    (A',
                     %Lam (u, Case ($u, (v1, `App (fB, `$v1)), (v2, `App (fC, `$v2)))),
                     %Lam (u, Inl (`App (gB, `$u))))
                  end
                | _ => 
                  let
                    val A' = Pr.Choice (Pr.Prop B', Pr.Prop C')
                  in
                    (A',
                     %Lam (u, Case ($u, (v1, Inl (`App (fB, `$v1))), (v2, Inr (`App (fC, `$v2))))),
                     %Lam (u, Case ($u, (v1, Inl (`App (gB, `$v1))), (v2, Inr (`App (gC, `$v2))))))
                  end)
          end
        | onf (Pr.Bang B) = 
          let
            val (B', fB, gB) = norm B
          in
            fresh2
            (fn (u, v) =>
                case B' of
                  Pr.One =>
                  let
                    val A' = Pr.One
                  in
                    (A',
                     %Lam (u, LetBang ($u, (v, `App (fB, `$v)))),
                     %Lam (u, LetOne ($u, Bang (`App (gB, One)))))
                  end
                | _ => 
                  let
                    val A' = Pr.Bang (Pr.Prop B')
                  in
                    (A',
                     %Lam (u, LetBang ($u, (v, Bang (`App (fB, `$v))))),
                     %Lam (u, LetBang ($u, (v, Bang (`App (gB, `$v))))))
                  end)
          end
        | onf (Pr.Brace B) = 
          let
            val (B', fB, gB) = norm B
          in
            fresh2
            (fn (u, v) =>
                case B' of
                  Pr.One =>
                  let
                    val A' = Pr.One
                  in
                    (A',
                     %Lam (u, Bra (LetBra ($u, (v, `App (fB, `$v))))),
                     %Lam (u, Bra (LetBra ($u, (v, `App (gB, One))))))
                  end
                | _ => 
                  let
                    val A' = Pr.Brace (Pr.Prop B')
                  in
                    (A',
                     %Lam (u, Bra (LetBra ($u, (v, `App (fB, `$v))))),
                     %Lam (u, Bra (LetBra ($u, (v, `App (gB, `$v))))))
                  end)
          end
        | onf P =                       (* atomics and constants *)
          let
            val B = Pr.Limp (Pr.Prop P, Pr.Prop P)
          in
            fresh (fn v => (P, %Lam (v, `$v), %Lam (v, `$v)))
          end
    in
      onf A
    end

local open P.Desc in
fun onf A =
    let
      val (A, f, g) = norm A

      fun doit_debug c =
          let
            val p = `App (g, c)
            val _ = Comm.send "onf1" (fn () => hBox [string "p = ", Proof.pp_chk p])
            val n = Timers.time1 Timers.validation Norm.cnorm p
            val _ = Comm.send "onf2" (fn () => hBox [string " n = ", Proof.pp_chk n])
            val r = Timers.time1 Timers.validation Proof.renumber n
            val _ = Comm.send "onf3" (fn () => hBox [string "r = ", Proof.pp_chk r])
          in
            r
          end

      fun doit c = Proof.renumber (Norm.cnorm (`App (g, c)))
      val doit = Timers.time1 Timers.validation doit_debug
    in
      (Pr.Prop A, doit)
    end
end

end
