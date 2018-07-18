structure ExtSyn =
struct

datatype cmd = Assume of string * Prop.prop
             | Prove of Prop.prop
             | Refute of int * Prop.prop
             | Left of string list
             | Right of string list
             | Check of Proof.chk * Prop.prop
             | Reject of Proof.chk * Prop.prop
             | Norm of Proof.chk
             | Prop of string
             | Channel of string
             | Bind of string * string
             | Log of string * string
             | Unlog of string
             | Include of string


local open P.Desc in

fun pp_cmd (Assume (n, P)) =
      hovBox (P.Rel 2, [string "assume", space 1, string n, space 1, string ":", space 1, Prop.pp_prop P])
  | pp_cmd (Prove P) =
      hovBox (P.Rel 2, [string "prove", space 1, Prop.pp_prop P])
  | pp_cmd (Left ls) = 
      hovBox (P.Rel 2, [string "left", space 1] @ P.delimit [string ",", space 1] string ls)
  | pp_cmd (Right ls) = 
      hovBox (P.Rel 2, [string "right", space 1] @ P.delimit [string ",", space 1] string ls)
  | pp_cmd (Refute (n, P)) =
      hovBox (P.Rel 2, [string "refute", space 1, string (Int.toString n), space 1, string ":", space 1, Prop.pp_prop P])
  | pp_cmd (Check (p, A)) = 
      hovBox (P.Rel 2, [string "%check", space 1, 
                       Proof.pp_chk p, space 1, string ":", space 1, Prop.pp_prop A])
  | pp_cmd (Reject (p, A)) = 
      hovBox (P.Rel 2, [string "%reject", space 1, 
                       Proof.pp_chk p, space 1, string ":", space 1, Prop.pp_prop A])
  | pp_cmd (Norm p) =
      hovBox (P.Rel 2, [string "%norm", space 1, Proof.pp_chk p])
  | pp_cmd (Prop P) = hBox [string P, space 1, string "prop"]
  | pp_cmd (Channel c) = hBox [string "%channel", space 1, string c]
  | pp_cmd (Bind (c, f)) = hBox [string "%bind", space 1,
                                 string c, space 1, string ":", space 1,
                                 string ("'" ^ f ^ "'")]
  | pp_cmd (Log (c, f)) = hBox [string "%log", space 1,
                                string c, space 1, string ":", space 1,
                                string f]
  | pp_cmd (Unlog c) = hBox [string "%unlog", space 1, string c]
  | pp_cmd (Include f) = hBox [string "%include", space 1, string ("'" ^ f ^ "'")]

end

end
