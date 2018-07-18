signature ERRORMSG =
  sig
    val reset : unit -> unit
      
    val anyErrors : bool ref
      
    val sourceStream : TextIO.instream ref
      
    val error : Mark.mark -> P.pp_desc -> unit
    val warn : Mark.mark -> P.pp_desc -> unit

    val error' : Mark.mark -> string -> unit
    val warn' : Mark.mark -> string -> unit
      
    exception Error
    val impossible : P.pp_desc -> 'a
    val impossible' : string -> 'a
  end

structure ErrorMsg :> ERRORMSG =
  struct
    (* Initial values of compiler state variables *)
    val anyErrors = ref false
    val sourceStream = ref TextIO.stdIn

    fun reset() = (anyErrors:=false; sourceStream:=TextIO.stdIn)

    fun s2dig n = String.concat [if n < 0 then "-" else "",
                                 Int.toString (Int.abs n)]
      
    open P.Desc
    fun msg str ext note =
          (anyErrors := true;
           P.pr (hBox [string (Mark.show ext), string ": ", string str, string ": ", note]))

    val error = msg "Error"
    val warn = msg "Warning"

    fun error' m n = error m (string n)
    fun warn' m n = warn m (string n)

    (* Print the given error message and then abort compilation *)
    exception Error
    fun impossible msg =
        (P.pr (hBox [string "!! BUG IN THEOREM PROVER !!", newline, msg]); raise Error)
    fun impossible' m = impossible (string m)
  end
