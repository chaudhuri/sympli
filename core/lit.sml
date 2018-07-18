(* 
 * Two-phase labelling
 * Author: Kaustuv Chaudhuri
 *)

structure Lit :> LIT =
struct

datatype sign = Pos | Neg

fun flip Pos = Neg
  | flip Neg = Pos


structure L = Label
structure LM = L.Map

open Prop

datatype mode = NORMAL | HEAVY | AFFINE

(* literals *)
datatype lit = LIT of {label : Label.label,  (* name of literal *)
                       skel : skel,          (* skeleton *)
                       sign : sign,
                       unr : bool ref,       (* descendant of ! *)
                       mode : mode ref}

withtype skel = lit Prop.skel

fun eq_lit (LIT L1, LIT L2) =
      eq_skel (#skel L1, #skel L2)
      andalso #sign L1 = #sign L2
      
and eq_skel (s1, s2) = Prop.eq_skel eq_lit (s1, s2)

fun skel (LIT {skel, ...}) = skel
fun sign (LIT {sign, ...}) = sign

fun set_heavy (LIT {mode, ...}) = mode := HEAVY
fun set_affine (LIT {mode, ...}) = mode := AFFINE

fun set_unr (LIT {unr, skel, ...}) =
    let
      fun set (Tensor (A, B)) = (set_unr A; set_unr B)
        | set (Limp (A, B)) = (set_unr A; set_unr B)
        | set (With (A, B)) = (set_unr A; set_unr B)
        | set (Choice (A, B)) = (set_unr A; set_unr B)
        | set (Bang A) = set_unr A
        | set _ = ()
    in
      unr := true;
      set skel
    end

val trivlab = L.named "__TRIVIAL__"
fun triv (Prop A) =
    let
      fun skel (Atomic P) = Atomic P
        | skel (Tensor (A, B)) = Tensor (triv A, triv B)
        | skel One = One
        | skel (Limp (A, B)) = Limp (triv A, triv B)
        | skel (With (A, B)) = With (triv A, triv B)
        | skel Top = Top
        | skel (Choice (A, B)) = Choice (triv A, triv B)
        | skel Zero = Zero
        | skel (Bang A) = Bang (triv A)
        | skel (Brace A) = Brace (triv A)
    in
      LIT {label = trivlab, skel = skel A, sign = Pos, unr = ref false, mode = ref NORMAL}
    end

fun triv' p =
    let val LIT {skel, ...} = triv p in skel end

structure Register =
  struct
    open L.Map

    val reg : lit L.map ref = ref empty
    fun reset () = reg := empty

    fun bind (l, skel) = reg := insert (!reg, l, skel)

    fun lookup l = find (!reg, l)

    fun skels () = listItems (!reg)
  end
structure R = Register

(* real labelling *)
fun label (Prop A, sign) =
    let
      fun for (Atomic P) = Atomic P
        | for (Tensor (A, B)) = Tensor (label (A, sign), label (B, sign))
        | for One = One
        | for (Limp (A, B)) = Limp (label (A, flip sign), label (B, sign))
        | for (With (A, B)) =
          let
            val la = label (A, sign)
          in
            (case B of Prop One => set_affine la | _ => ());
            With (la, label (B, sign))
          end
        | for Top = Top
        | for (Choice (A, B)) = Choice (label (A, sign), label (B, sign))
        | for Zero = Zero
        | for (Bang A) = 
          let
            val la = label (A, sign)
          in
            set_heavy la;
            set_unr la;
            Bang la
          end
        | for (Brace A) = Brace (label (A, sign))

      val l = case A of Atomic P => L.named' P | _ => L.new ()
      val skel = for A
      val lit = LIT {label = l, skel = skel, sign = sign, unr = ref false, mode = ref NORMAL}
    in
      if not (L.is_named l) then R.bind (l, lit) else ();
      lit
    end

(* pretty printing *)
open P.Desc

fun pp_mode NORMAL = string "normal"
  | pp_mode HEAVY = string "heavy"
  | pp_mode AFFINE = string "affine"

fun pp depth (LIT {label, skel, sign, unr = ref unr, mode = ref mode}) =
      hBox [Label.pp label, string " = {",
            hvBox (P.Rel 0,
                   [pp_skel depth skel, string ";", space 1,
                    pp_sign sign, string ";", space 1,
                    string (if unr then "unr" else "lin"), string ";", space 1,
                    pp_mode mode, cut]),
            string "}"]

and itemize_lit depth (LIT {label, skel, ...}) =
    if depth > 0 then itemize_skel (itemize_lit (depth - 1)) skel
    else P.Atm (Label.pp label)

and pp_sign Pos = string "+"
  | pp_sign Neg = string "-"

and pp_skel depth skel = P.lineate (itemize_skel (itemize_lit (depth - 1)) skel)

end
