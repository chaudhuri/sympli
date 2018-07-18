structure Parse =
struct

local
structure PropLrVals = PropLrValsFun (structure Token = LrParser.Token)
structure PropLex = PropLexFun (structure Tokens = PropLrVals.Tokens)

structure PropParser = JoinWithArg (structure ParserData = PropLrVals.ParserData
                                    structure Lex = PropLex
                                    structure LrParser = LrParser)

(* The main parsing routine *)
fun phase errors filename =
    let
	val file = TextIO.openIn filename
	fun get _ = TextIO.input file
	fun parseerror(s,p1,p2) =
              ErrorMsg.error' (Mark.mark {left = p1, right = p2, file = filename}) s
              before errors := true
	val lexer = LrParser.Stream.streamify (PropLex.makeLexer get (PropLex.UserDeclarations.init ()))
	val (absyn, _) = PropParser.parse (15, lexer, parseerror, filename)
        val _ = TextIO.closeIn file;
    in
      includes errors absyn
    end
      handle LrParser.ParseError => raise ErrorMsg.Error
           | e as IO.Io _ => (ErrorMsg.error' Mark.unknown (exnMessage e);
                              raise ErrorMsg.Error)

and includes errors ((ExtSyn.Include f, _) :: more) =
      phase errors f @ includes errors more
  | includes errors (l :: more) = 
      l :: includes errors more
  | includes errors nil = nil

fun parse f =
    let
      val _ = ErrorMsg.reset ()
      val errors = ref false
    in
      (phase errors f, !errors)
    end
in

val parse = Timers.time1 Timers.parsing parse

end

end
