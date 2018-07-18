structure StringDev :> 
  sig
    include PP_DEVICE where type style = StringToken.style
    val new : unit -> device
    val get : device -> string
  end =
  struct
    type device = string list ref

    type style = StringToken.style

    fun sameStyle (s1, s2) = true
    fun pushStyle (d, s) = ()
    fun popStyle d = ()

    fun defaultStyle d = ()

    fun depth d = NONE
    fun lineWidth d = SOME 80
    fun textWidth d = SOME 80

    fun space (d, n) = d := String.implode (List.tabulate (n, fn _ => #" ")) :: (!d)
    fun newline d = d := "\n" :: (!d)

    fun string (d, s) = d := s :: (!d)
    fun char (d, c) = d := Char.toString c :: (!d)

    fun flush d = ()

    fun new () = ref []
    fun get d = (String.concat o List.rev) (!d)
  end

structure P =
struct

local 
  structure PP = PPStreamFn (structure Token = StringToken
                             structure Device = StringDev)
in
  open PP
  structure Desc = PPDescFn(PP)
  open Desc
end

fun delimit (sep : pp_desc list) (f : 'a -> pp_desc) (l : 'a list) =
    let
      val sep = List.rev sep
      fun delimit' [] res = res
        | delimit' [l] res = f l :: res
        | delimit' (h :: t) res = delimit' t (sep @ [f h] @ res)
    in
      List.rev (delimit' l [])
    end

fun unparse dsc =
    let
      val dev = StringDev.new ()
      val ppstrm = openStream (dev)
    in
      description (ppstrm, dsc);
      closeStream ppstrm;
      StringDev.get dev
    end

fun pr dsc =
    let
      val d = unparse dsc
    in
      TextIO.output (TextIO.stdOut, d ^ "\n")
    end

datatype assoc = Left | Right

datatype opr  = Infix of int * assoc * item * item
              | Prefix of int * item 

     and item = Opr of opr * pp_desc
              | Atm of pp_desc
              | Bra of pp_desc * item * pp_desc


local

open Desc
  fun bracket p = hBox [string "(", p, string ")"]

  fun lineate (Atm p) = p
    | lineate (Opr (tr, opp)) = 
        lineate_opr opp tr
    | lineate (Bra (l, A, r)) = 
        hBox [l, lineate A, r]

  and lineate_opr opp (Prefix (prec, item)) =
      let
        val p = lineate item
      in
        hvBox (Rel 2, [opp, if precomp (item, prec) = LESS then bracket p else p])
      end
    | lineate_opr opp (Infix (prec, ass, A, B)) = 
      let
        val Ap = lineate A
        val Bp = lineate B
      in
        hvBox (Rel 2, [case (precomp (A, prec), ass) of
                           (LESS, _) => bracket Ap
                         | (EQUAL, Right) => bracket Ap
                         | _ => Ap,
                         space 1, opp, space 1,
                         if isprefix B then Bp
                         else case (precomp (B, prec), ass) of
                                (LESS, _) => bracket Bp
                              | (EQUAL, Left) => bracket Bp
                              | _ => Bp])
      end

  and isprefix (Opr (Prefix _, _)) = true
    | isprefix _ = false

  and precomp (Atm _, p) = GREATER
    | precomp (Bra _, p) = GREATER
    | precomp (Opr (Prefix (p, _), _), p') = Int.compare (p, p')
    | precomp (Opr (Infix (p, _, _, _), _), p') = Int.compare (p, p')
in
val lineate = lineate
end


end
