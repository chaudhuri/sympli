signature TOP =
sig
    val doit : string -> unit
    val export : string * string list -> OS.Process.status
end

structure Top :> TOP =
struct

exception Top

open P.Desc ExtSyn

datatype lit = datatype Lit.lit

fun pp_marked (c, m) =
      Comm.send "cfg" (fn () => hBox [string "(* from ",
                                      string (Mark.show m),
                                      string " *)", newline,
                                      pp_cmd c])

fun tackle (c, m) =
    let
      fun process (Prove A) =
          (case Engine.prove (A, false, 0) of
             SOME prf => (Comm.send "term" (fn () => vBox (P.Rel 0,
                                                           [string "\t(* proof term follows *)", cut, cut,
                                                            Proof.pp_chk prf, cut]));
                          Proof.test (Proof.ctx ([], []), prf, SOME (Lit.triv' A), false);
                          Comm.send "validation" (fn () => string "\t(* certificate OK *)"))
           | NONE => (Comm.send "cfg" (fn () => string "\t(* NO PROOF FOUND *)");
                      raise Top)) before Timers.check ()
        | process (Refute (n, A)) = (Engine.prove (A, true, n); Timers.check ())
        | process (Left names) =
            List.app (fn x => Bias.setbias (Atom.atom x, Bias.Left)) names
        | process (Right names) =
            List.app (fn x => Bias.setbias (Atom.atom x, Bias.Right)) names
        | process (Channel ch) = Comm.bind {chan = ch, file = "-"}
        | process (Bind (ch, f)) = Comm.bind {file = f, chan = ch}
        | process (Log (wh, ch)) = Comm.log {chan = ch, what = wh}
        | process (Unlog wh) = Comm.unlog wh
        | process (Check (p, A)) =
          (Proof.test (Proof.ctx ([], []), p, SOME (Lit.triv' A), false);
           Comm.send "cfg" (fn () => string "\t(* OK *)");
           Timers.check ())
        | process (Reject (p, A)) =
          ((Proof.test (Proof.ctx ([], []), p, SOME (Lit.triv' A), false);
            Comm.send "cfg" (fn () => string "\t(* FAILED TO REJECT *)");
            raise Top) handle Proof.Check => Comm.send "cfg" (fn () => string "\t(* rejected in CHECK phase *)")
                            | Proof.Infer => Comm.send "cfg" (fn () => string "\t(* rejected in INFER phase *)"))
            before Timers.check ()
        | process (Norm c) = 
          let
            val n = Timers.time1 Timers.validation Norm.cnorm c
          in
            Comm.send "cfg" (fn () => hBox [string "normal_form: ", Proof.pp_chk n])
          end
        | process _ = Comm.send "cfg" (fn () => string "\t(* IGNORING *)")
    in
      pp_marked (c, m);
      process c
    end
             
fun resets () =
    (Label.reset ();
     Var.reset ();
     Timers.reset ();
     Comm.reset ())

fun doit' f =
    let
      val (cfg, errors) = Parse.parse f
    in
      if errors then raise Top
      else List.app tackle cfg
    end

fun doit f = (resets (); doit' f)
            
fun printBias b = TextIO.output (TextIO.stdErr, "Bias set to " ^ (if b = Bias.Left then "LEFT" else "RIGHT") ^ "\n")

fun export (name, args) =
    (case args of
      "-left" :: args => (Bias.default := Bias.Left; export' args)
    | "-right" :: args => (Bias.default := Bias.Right; export' args)
    | _ => export' args)

and export' args =
    let in
      printBias (!Bias.default);
      resets ();
      List.app doit args;
      OS.Process.success
    end handle e => (P.pr (hBox [string "ABORT: ", string (exnMessage e)]); OS.Process.failure)

end
