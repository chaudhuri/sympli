signature MARK =
  sig
    type mark


    val unknown : mark
    val mark : {left : int * int,
                right : int * int,
                file : string} -> mark

    val show : mark -> string
  end

structure Mark :> MARK =
struct
datatype mark = MARK of {left : int * int,
                         right : int * int,
                         file : string} option

val unknown = MARK NONE
val mark = MARK o SOME

fun pos (line, col) = Int.toString line ^ "." ^ Int.toString col

fun show (MARK NONE) = "unknown"
  | show (MARK (SOME {left, right, file})) = file ^ ":" ^ pos left ^ "-" ^ pos right
end

(*
 * Local Variables:
 * fill-column: 80
 * sml-compile-command: "CM.make \"../sources.cm\""
 * End:
 *)
