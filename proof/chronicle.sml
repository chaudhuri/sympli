(* 
 * Proof chronicles
 * Author: Kaustuv Chaudhuri
 *)

structure Chronicle :> CHRONICLE =
struct 

type label = Label.label

datatype chronicle = 
         Init of label

       | Copy of label * chronicle

       | TensR of label list * chronicle * chronicle
       | TensL of label * chronicle

       | OneR
       | OneL of label * chronicle

       | LimpR of chronicle
       | LimpL of label list * label * chronicle * chronicle

       | WithR of chronicle * chronicle
       | WithL1 of label * chronicle
       | WithL2 of label * chronicle

       | TopR

       | ChoiceR1 of chronicle
       | ChoiceR2 of chronicle
       | ChoiceL of label * chronicle * chronicle

       | ZeroL of label

       | BangR of chronicle
       | BangL of label * chronicle

       | BraceR of chronicle
       | BraceL of label * chronicle

open P.Desc

val pp_label = Label.pp

fun pp (Init l) = hBox [string "Init (", pp_label l, string ")"]
  | pp (Copy (l, ch)) = 
      hvBox (P.Rel 0, [string "Copy (", pp_label l, string ",", space 1, pp ch, string ")"])
  | pp (TensR (ls, ch1, ch2)) =
      hvBox (P.Rel 0, [string "TensR (",
                       hBox [string "[", hovBox (P.Rel 0, P.delimit [string ",", space 1] pp_label ls), string "]"],
                       string ",", space 1,
                       pp ch1,
                       string ",", space 2,
                       pp ch2, string ")"])
  | pp (TensL (l, ch)) = 
      hvBox (P.Rel 0, [string "TensL (",
                       pp_label l,
                       string ",", space 1,
                       pp ch, string ")"])
  | pp OneR = string "OneR"
  | pp (OneL (l, ch)) =
      hvBox (P.Rel 0, [string "OneL (",
                       pp_label l,
                       string ",", space 1,
                       pp ch, string ")"])
  | pp (LimpR ch) = hBox [string "LimpR (", pp ch, string ")"]
  | pp (LimpL (ls, l, ch1, ch2)) = 
      hvBox (P.Rel 0, [string "LimpL (",
                       hBox [string "[", hovBox (P.Rel 0, P.delimit [string ",", space 1] pp_label ls), string "]"],
                       string ",", space 1,
                       pp_label l,
                       string ",", space 1,
                       pp ch1,
                       string ",", space 2,
                       pp ch2, string ")"])
  | pp (WithR (ch1, ch2)) =
      hvBox (P.Rel 0, [string "WithR (",
                       pp ch1,
                       string ",", space 1,
                       pp ch2, string ")"])
  | pp (WithL1 (l, ch)) = 
      hvBox (P.Rel 0, [string "WithL1 (",
                       pp_label l,
                       string ",", space 1,
                       pp ch, string ")"])
  | pp (WithL2 (l, ch)) = 
      hvBox (P.Rel 0, [string "WithL2 (",
                       pp_label l,
                       string ",", space 1,
                       pp ch, string ")"])
  | pp TopR = string "TopR"
  | pp (ChoiceR1 ch) = hBox [string "ChoiceR1 (", pp ch, string ")"]
  | pp (ChoiceR2 ch) = hBox [string "ChoiceR2 (", pp ch, string ")"]
  | pp (ChoiceL (l, ch1, ch2)) =
      hvBox (P.Rel 0, [string "ChoiceL (",
                       pp_label l,
                       string ",", space 1,
                       pp ch1,
                       string ",", space 2,
                       pp ch2, string ")"])
  | pp (ZeroL l) = hBox [string "ZeroL (", pp_label l, string ")"]
  | pp (BangR ch) = hBox [string "BangR (", pp ch, string ")"]
  | pp (BangL (l, ch)) = 
      hvBox (P.Rel 0, [string "BangL (",
                       pp_label l,
                       string ",", space 1,
                       pp ch, string ")"])
  | pp (BraceR ch) = hBox [string "BraceR (", pp ch, string ")"]
  | pp (BraceL (l, ch)) = 
      hvBox (P.Rel 0, [string "BraceL (",
                       pp_label l,
                       string ",", space 1,
                       pp ch, string ")"])

end
