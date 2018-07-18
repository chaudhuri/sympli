signature FOLD_HEUR =
sig
  (* fire r: should r be substituted for bound variables? *)
  val fire : Proof.inf -> bool
end

structure Fold :
          sig
            structure Never : FOLD_HEUR
            structure Always : FOLD_HEUR
            structure Rename : FOLD_HEUR
          end =
struct
  structure Never =
  struct
    fun fire r = false
  end

  structure Always =
  struct
    fun fire r = true
  end

  structure Rename = 
  struct
    (* 
     * for cases like "let x = y in c end", the
     * extra binding doesn't increase sharing in
     * the term in any fashion; such cases should
     * be folded.
     *)
    fun fire (Proof.Var _) = true
      | fire _ = false
  end
end
