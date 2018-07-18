(* 
 * Sequents
 * Author: Kaustuv Chaudhuri
 *)

structure Sequent :> SEQUENT =
struct

structure L = Label
structure LM = L.Map

structure C = Chronicle

type label = L.label

type ctx = int L.map
type right = L.label option * bool
type left = ctx * ctx * ctx

type sequent' = {left : left, right : right, weak : bool}
datatype sequent = SEQUENT of {left : left,
                               right : right,
                               weak : bool,
                               chron : C.chronicle}

fun eq_sequent (SEQUENT S1, SEQUENT S2) =
      eq_left (#left S1, #left S2)
      andalso eq_right (#right S1, #right S2)
      andalso #weak S1 = #weak S2

and eq_left ((G1, P1, D1), (G2, P2, D2)) =
      eq_ctx (G1, G2)
      andalso eq_ctx (P1, P2)
      andalso eq_ctx (D1, D2)

and eq_ctx (C1, C2) =
    let
      val C1l = LM.listItemsi C1
      val C2l = LM.listItemsi C2
    
      fun check (nil, nil) = true
        | check ((L1, n1) :: more1, (L2, n2) :: more2) = 
            L.eq (L1, L2) andalso n1 = n2 andalso check (more1, more2)
        | check _ = false
    in
      check (C1l, C2l)
    end

and eq_right ((L1, b1), (L2, b2)) =
    let
      fun eq (SOME L1, SOME L2) = L.eq (L1, L2)
        | eq (NONE, NONE) = true
        | eq _ = false
    in
      eq (L1, L2) andalso b1 = b2
    end

(* renaming *)

fun rename_ctx c = c
                                          
fun rename (SEQUENT {left = (unr, aff, lin), right, weak, chron}) =
      SEQUENT {left = (rename_ctx unr, rename_ctx aff, rename_ctx lin),
               right = right,
               weak = weak,
               chron = chron}


exception Partial

(* factor *)

fun factor (SEQUENT {left = (unr, aff, lin), right, weak, chron}) =
    let
      val unr = LM.map (fn n => 1) unr
    in
      SEQUENT {left = (unr, aff, lin),
               right = right,
               weak = weak,
               chron = chron}
    end

(* extraction *)

fun extract strict (G, l) =
    (case LM.find (G, l) of
       SOME 1 => (SOME (#1 (LM.remove (G, l))), false)
     | SOME n => (SOME (LM.insert (G, l, n - 1)), false)
     | NONE => if strict then (NONE, false) else (SOME G, true))


datatype emode = STRICT | NORMAL | LAX

fun remove em (left, Lit.LIT L) =
    (case #skel L of
       Prop.Bang (Lit.LIT La) => remove_unr em left (#label La, #label L)
     | Prop.With (Lit.LIT La, Lit.LIT Lb) =>
       (case (#skel La, #skel Lb) of
          (_, Prop.One) => remove_aff em left (#label La, #label Lb, #label L)
        | _ => remove_lin em left (#label L))
     | _ => remove_lin em left (#label L))

and remove_unr em (unr, aff, lin) (l, lfin) =
    (case extract (em = STRICT) (unr, l) of
       (SOME unr, fresh) => SOME {left = (unr, aff, lin), fresh = false, refl = fn ch => C.BangL (lfin, ch)}
     | _ => NONE)

and remove_aff em (unr, aff, lin) (la, l1, lfin) =
    (case extract true (aff, la) of
       (SOME aff, fresh) =>
         SOME {left = (unr, aff, lin), fresh = false, refl = fn ch => C.WithL1 (lfin, ch)}
     | (NONE, fresh) =>
         if em = STRICT then NONE
         else SOME {left = (unr, aff, lin), fresh = false, refl = fn ch => C.WithL2 (lfin, C.OneL (l1, ch))})

and remove_lin em (unr, aff, lin) l =
    (case extract (em <> LAX) (lin, l) of
       (SOME lin, fresh) => SOME {left = (unr, aff, lin), fresh = fresh, refl = fn ch => ch}
     | _ => NONE)

(* muultiplicative join *)

fun concat (c1, c2) = LM.unionWith Int.+ (c1, c2)

fun concat_noninter (c1, c2) =
      LM.unionWithi (fn (l, m, n) =>
                        let in
                          if not (Label.is_named l) then
                            (case Lit.Register.lookup l of
                               SOME (Lit.LIT {unr, ...}) =>
                                 if !unr then m + n else raise Partial
                             | NONE => m + n)
                          else m + n
                        end)
                    (c1, c2)

fun join ((unr1, aff1, lin1), (unr2, aff2, lin2)) =
      (concat (unr1, unr2), concat_noninter (aff1, aff2), concat_noninter (lin1, lin2))

fun join' (left1, L) = join (left1, (LM.empty, LM.empty, LM.digest [(L, 1)]))

    
(* additive join *)

val Add = Partial

fun any_match (c1, c2) = LM.unionWith Int.max (c1, c2)
fun left_prefix (c1, c2) =
      LM.mergeWith (fn (NONE, k) => k
                     | (SOME k, SOME l) => if k > l then raise Add else SOME l
                     | _ => raise Add) (c1, c2)
fun right_prefix (c1, c2) =
      LM.mergeWith (fn (k, NONE) => k
                     | (SOME k, SOME l) => if k < l then raise Add else SOME k
                     | _ => raise Add) (c1, c2)
fun exact_match (c1 : ctx, c2 : ctx) =
      LM.mergeWith (fn (SOME k, SOME l) => if k <> l then raise Add else SOME k
                     | _ => raise Add) (c1, c2)

fun weak_eq (lin1, true) (lin2, true) = any_match (lin1, lin2)
  | weak_eq (lin1, true) (lin2, false) = left_prefix (lin1, lin2)
  | weak_eq (lin1, false) (lin2, true) = right_prefix (lin1, lin2)
  | weak_eq (lin1, false) (lin2, false) = exact_match (lin1, lin2)


fun add (((unr1, aff1, lin1), weak1), ((unr2, aff2, lin2), weak2)) =
    let
      val lin = weak_eq (lin1, weak1) (lin2, weak2)
      val aff = weak_eq (aff1, true) (aff2, true)
      val unr = concat (unr1, unr2)
    in
      (unr, aff, lin)
    end



(* subsumption *)

fun subsumes (S1, SEQUENT S2) =
      subsumes' S1 {left = #left S2, right = #right S2, weak = #weak S2}

and subsumes' S1 foo = subsumes'' S1 foo

and subsumes'' (SEQUENT S1) {left, right, weak} =
    let
      val (G1, P1, D1) = #left S1
      val (G2, P2, D2) = left
    in
      (* filter #1: there must be fewer things on the left *)
      LM.numItems D1 <= LM.numItems D2
      andalso LM.numItems P1 <= LM.numItems P2
      andalso LM.numItems G1 <= LM.numItems G2

      (* original subsumption check *)
      andalso (case (#weak S1, weak) of
                 (true, _) => subsumes_ctx (D1, D2)
               | (false, false) => eq_ctx (D1, D2)
               | _ => false)
      andalso subsumes_ctx (G1, G2)
      andalso subsumes_ctx (P1, P2)
      andalso subsumes_right (#right S1, right)
    end

and subsumes_ctx (G1, G2) =
    let
      exception Abort
    in 
      (LM.appi (fn (l, n1) => (case LM.find (G2, l) of
                                  SOME n2 => if n2 < n1 then raise Abort else ()
                                | NONE => raise Abort)) G1;
       true) handle Abort => false
    end

and subsumes_right ((L1, b1), (L2, b2)) =
    let
      fun lsub (NONE, _) = true
        | lsub (SOME l1, SOME l2) = L.eq (l1, l2)
        | lsub _ = false

      fun imp (false, _) = true
        | imp (true, b) = b = true
    in
      lsub (L1, L2) andalso imp (b1, b2)
    end


(* validation *)
fun proof (seq as SEQUENT {left = (unr, aff, lin), right as (rightL, rightB), chron, ...}) =
    let
      fun mk_zone Z = 
            LM.mapi (fn (l, n) =>
                        case Lit.Register.lookup l of
                          SOME (Lit.LIT {skel, ...}) =>
                            List.tabulate (n, fn _ => (Var.fresh "proof", skel))
                        | NONE => raise Fail "proof") Z
                    
      val uzone = mk_zone unr
      val lzone = LM.unionWith List.@ (mk_zone aff, mk_zone lin)
      val r = (case Option.join (Option.map Lit.Register.lookup rightL) of
                 SOME (Lit.LIT {skel, ...}) => SOME skel
               | _ => NONE)

      val prf = ProofBuild.build (uzone, lzone, r) chron

      val uctx = List.concat (LM.listItems uzone)
      val lctx = List.concat (LM.listItems lzone)

      val ctx = Proof.ctx (uctx, lctx)

      val r = (case rightL of
                 SOME l => (case Lit.Register.lookup l of
                              SOME (Lit.LIT {skel, ...}) => SOME skel
                            | NONE => NONE)
               | NONE => NONE)
    in
      (ctx, prf, r, rightB)
    end

fun valid seq = Proof.test (proof seq)

(* pretty printing *)


open P.Desc

fun flatten z =
      LM.foldri (fn (l, n, flat) =>
                    List.tabulate (n, fn _ => l) @ flat) [] z

fun pp_elem l =
    (case Lit.Register.lookup l of
       SOME (Lit.LIT {skel, ...}) => Lit.pp_skel 2 skel
     | _ => L.pp l)

fun pp_ctx z = hovBox (P.Rel 0, P.delimit [string ",", space 1] pp_elem (flatten z))

fun pp_right (L, b) =
    let
      fun ppr (SOME l) = L.pp l
        | ppr NONE = string "."
    in
      if b then hBox [ppr L, string " lax"] else ppr L
    end

fun pp_sequent (SEQUENT {left = (unr, aff, lin),
                         right, weak, ...}) =
      hovBox (P.Rel 2,
              [pp_ctx unr,
               space 1, string ";", space 1,
               pp_ctx aff,
               space 1, string ";", space 1,
               pp_ctx lin,
               space 1, string "-->", string (if weak then "1" else "0"), space 1,
               pp_right right])

fun pp_sequent' {left = (unr, aff, lin), right, weak} =
      hovBox (P.Rel 2,
              [pp_ctx unr,
               space 1, string ";", space 1,
               pp_ctx aff,
               space 1, string ";", space 1,
               pp_ctx lin,
               space 1, string "-->", string (if weak then "1" else "0"), space 1,
               pp_right right])


end
