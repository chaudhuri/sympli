signature COMM =
sig
  val reset : unit -> unit

  val send : string -> (unit -> P.pp_desc) -> unit

  val error : P.pp_desc -> unit

  exception Comm
  val bind : {chan : string, file : string} -> unit
  val log : {what : string, chan : string} -> unit
  val unlog : string -> unit
end

structure Comm :> COMM =
struct

open P.Desc

structure SM = MapFn (struct
                        open String
                        type ord_key = string
                        val pp = P.Desc.string
                      end)

exception Comm

val chans : TextIO.outstream option SM.map ref = ref SM.empty
val logs : string SM.map ref = ref SM.empty

fun bind {chan, file = "-"} = chans := SM.insert (!chans, chan, NONE)
  | bind {chan, file} = 
    let
      val _ = Option.map (Option.map TextIO.closeOut) (SM.find (!chans, chan))
      val f = TextIO.openOut file
    in
      chans := SM.insert (!chans, chan, SOME f)
    end


fun log {what, chan} =
    if SM.inDomain (!chans, chan) then
      logs := SM.insert (!logs, what, chan)
    else (P.pr (hBox [string "no such channel '", string chan, string "'"]); raise Comm)
       

fun unlog what =
    (case SM.find (!logs, what) of
       SOME _ => logs := #1 (SM.remove (!logs, what))
     | _ => ())

fun reset () =
      (SM.map (Option.map TextIO.closeOut) (!chans);
       chans := SM.empty;
       logs := SM.empty;
       bind {chan = "error", file = "-"};
       log {what = "error", chan = "error"};
       bind {chan = "highlevel", file = "-"};
       log {what = "cfg", chan = "highlevel"})
    
val _ = reset ()

fun send to msg =
    (case SM.find (!logs, to) of
       SOME chan => 
         (case SM.find (!chans, chan) of
            SOME chan => (let
                            val str = Option.getOpt (chan, TextIO.stdOut)
                          in
                            TextIO.output (str, P.unparse (msg ()));
                            TextIO.output (str, "\n");
                            TextIO.flushOut  str
                          end)
          | _ => (P.pr (hBox [string "BUG!! log ", string to, string " bound to nonexistent channel ", string chan]);
                  raise Comm))
     | _ => ())

fun error msg = (TextIO.output (TextIO.stdErr, P.unparse msg);
                 TextIO.output (TextIO.stdErr, "\n"))

end
