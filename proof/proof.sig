(* Proof terms *)

signature PROOF =
sig

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

(* checking error *)
exception Check

(* inference error *)
exception Infer

(* unrestricted zone *)
type unr

(* linear zone *)
type lin

(* checking/infering context *)
type ctx = unr * lin

(* 
 * Assemble a ctx from a linearized representation.
 * Note: all variables in the input must be unique.
 *)
val ctx : (var * Lit.skel) list * (var * Lit.skel) list -> ctx

(* 
 * If    check (G, Di) (c, P, lx) = (s, Do)
 * Then  G ; Di \ Do |-s  c <== P lx
 *
 * If    infer (G, Di) i = (P, s, Do)
 * Then  G ; Di \ Do |-s  i ==> P
 *)
val check : ctx -> (chk * Lit.skel option * bool) -> bool * lin
val infer : ctx -> inf -> Lit.skel * bool * lin


(* 
 * test (G, D) (c, P, lx) = { true    if G ; D \ . |-s  c <== P lx
 *                          {            for some s
 *                          {
 *                          { false   otherwise
 *)
val test : ctx * chk * Lit.skel option * bool -> bool

(* 
 * renumber the bound variables for display purposes
 * If     G ; D |-s  c <== P
 * Then   G ; D |-s  renumber c <== P
 *)
val renumber : chk -> chk

(* pretty-printing *)
val pp_inf : inf -> P.pp_desc
val pp_chk : chk -> P.pp_desc
val pp_unr : unr -> P.pp_desc
val pp_lin : lin -> P.pp_desc
val pp_ctx : ctx -> P.pp_desc

end
