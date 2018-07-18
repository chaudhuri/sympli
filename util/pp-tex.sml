signature TEX_DEVICE =
sig
  datatype texstyle = HBOX
                    | RM | IT | TT
                    | UL | OL
                    | MATH
                    | GROUP | NOSTYLE

  include PP_DEVICE where type style = texstyle

  val new : unit -> device
  val print : device * string -> unit
  val show : device -> unit

  val raw : device -> string

end

structure TeXDevice :> TEX_DEVICE =
struct

infixr 0 $
fun f $ x = f x
fun whisper s = TextIO.output (TextIO.stdErr, s)
fun say s = TextIO.output (TextIO.stdErr, s ^ "\n")
fun shout s = say ("*** " ^ String.map Char.toUpper s ^ " ***")

datatype texstyle = HBOX
                  | RM | IT | TT
                  | UL | OL
                  | MATH
                  | GROUP | NOSTYLE

fun style_open HBOX = "\\hbox{"
  | style_open RM = "{\\rm"
  | style_open IT = "{\\it"
  | style_open TT = "{\\tt"
  | style_open UL = "\\underline{"
  | style_open OL = "\\overline{"
  | style_open MATH = "\\ensuremath{"
  | style_open GROUP = "{"
  | style_open NOSTYLE = ""

fun style_close [] = ErrorMsg.impossible "can't close this style"
  | style_close (NOSTYLE :: _) = ""
  | style_close _ = "}"

datatype device = DEV of {text : string list ref,
                          std : texstyle list ref}

fun new () = DEV {text = ref [],
                  std = ref []}

val header =
    "\\documentclass{article}\n" ^
    "\\usepackage{xspace,enumerate,fullpage}\n" ^
    "\\usepackage{amsmath}\n" ^
    "\\usepackage{pxfonts}\n" ^
    "\\setlength{\\parindent}{0pt}" ^
    "\\begin{document}\n"

val footer = "\n\\end{document}\n"

fun raw (DEV {text, std, ...}) = String.concat (rev $ !text);

fun print (DEV {text, std, ...}, file) =
    let
      val f = TextIO.openOut file
    in
      TextIO.output (f, header);
      List.app (fn s => TextIO.output (f, s)) (rev $ !text);
      while !std <> [] do (TextIO.output (f, style_close (!std)); std := tl (!std));
      TextIO.output (f, footer);
      TextIO.closeOut f
    end

exception ABORT

fun system name args =
    let in
      say $ "running: " ^ name ^ List.foldr (fn (a, x) => a ^ " " ^ x) "" args;
      (case Posix.Process.fork () of
         NONE =>
         (Posix.Process.execp (name, name :: args)
          handle e => (shout ("call to " ^ name ^ " aborted"); OS.Process.exit OS.Process.failure))
       | SOME pid => 
         (case (Posix.Process.waitpid (Posix.Process.W_CHILD pid, [])
                handle e => (shout "wait for child process failed";
                             say (exnMessage e);
                             raise ABORT)) of
            (_, Posix.Process.W_EXITED) => ()
          | (_, Posix.Process.W_EXITSTATUS stat) => 
            (shout ("child exited with status " ^ Word8.toString stat); raise ABORT)
          | _ => (shout ("child stopped or exited because of a signal"))))
    end

fun show dev =
    let
      val tmp = OS.FileSys.tmpName ()
      val cwd = OS.FileSys.getDir ()
    in
      print (dev, tmp ^ ".tex");
      OS.FileSys.chDir "/tmp";
      system "latex" ["\\nonstopmode\\input " ^ tmp];
      OS.FileSys.chDir cwd;
      system "xdvi" [tmp];
      OS.FileSys.remove $ tmp ^ ".tex";
      OS.FileSys.remove $ tmp ^ ".dvi";
      OS.FileSys.remove $ tmp ^ ".log";
      OS.FileSys.remove $ tmp ^ ".aux"
    end

type style = texstyle

(* val sameStyle : style * style -> bool *)
fun sameStyle (s1, s2) = s1 = s2

(* val pushStyle : device * style -> unit *)
fun pushStyle (DEV {text, std, ...}, st) =
    let
      val ostr = style_open st
    in
      text := ostr :: (!text);
      std := st :: (!std)
    end

(* val popStyle : device -> unit *)
fun popStyle (DEV {text, std, ...}) =
    let in
      text := style_close (!std) :: (!text);
      std := tl (!std)
    end

(* val defaultStyle : device -> style *)
fun defaultStyle _ = GROUP

(* val depth : device -> int option *)
fun depth _ = NONE

(* val lineWidth : device -> int option *)
fun lineWidth _ = SOME 65536

(* val textWidth : device -> int option *)
fun textWidth _ = SOME 65536

(* val space : device * int -> unit *)
fun space (DEV {text, ...}, n) =
    let in
      text := (if n = 1 then " "
               else "\\hspace{" ^ Int.toString n ^ "ex}") :: (!text)
    end

(* val newline : device -> unit *)
fun newline (DEV {text, std, ...}) =
    let in
      text := (* (if !math then "}\\newline\n\\ensuremath{" else "\\newline") *) "\\newline{}" :: (!text)
    end

fun sanitize s =
      String.concat
        $
        List.map (fn #"_" => "\\_"
                   | c => Option.valOf $ String.fromString $ Char.toString c)
        $
        String.explode s
                    

(* val string : device * string -> unit *)
fun string (DEV {text, ...}, s) =
    let in
      text := sanitize s :: (!text)
    end

(* val char : device * char -> unit *)
fun char (DEV {text, ...}, s) =
    let in
      text := sanitize (Char.toString s) :: (!text)
    end

(* val flush : device -> unit *)
fun flush _ = ()


end


structure TeXToken :> 
          sig
            datatype tok = CMD of string
                         | LEFT of string
                         | RIGHT of string

            include PP_TOKEN where type token = tok and type style = TeXDevice.style
          end =
struct

datatype tok = CMD of string
             | LEFT of string
             | RIGHT of string
                        
type token = tok
type style = TeXDevice.style

fun string (CMD x) = x
  | string (LEFT x) = "\\left" ^ x
  | string (RIGHT x) = "\\right" ^ x

fun style x = TeXDevice.NOSTYLE

fun size _ = 1

end


structure PT =
struct

structure PP = PPStreamFn (structure Token = TeXToken
                           structure Device = TeXDevice)

datatype style = datatype TeXDevice.texstyle
datatype token = datatype TeXToken.tok

open PP

fun delimit sep f l =
    let
      fun delimit' [] res = res
        | delimit' [l] res = f l :: res
        | delimit' (h :: t) res = delimit' t ([sep, f h] @ res)
    in
      Desc.hovBox (Rel 0, List.rev (delimit' l []))
    end

fun unparse dsc =
    let
      val dev = TeXDevice.new ()
      val ppstrm = openStream (dev)
    in
      description ppstrm dsc;
      closeStream ppstrm;
      dev
    end

fun show dsc = TeXDevice.show (unparse dsc)

fun pr (dsc, file) = TeXDevice.print (unparse dsc, file)

fun raw dsc = TeXDevice.raw (unparse dsc)

end
