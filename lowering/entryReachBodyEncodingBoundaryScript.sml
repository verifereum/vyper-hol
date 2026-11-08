Theory entryReachBodyEncodingBoundary
Ancestors
  vyperABI vyperInterpreter vyperTyping vyperValueOperation vyperValue
  finite_map list

(* Encoding is not injective on arbitrary source representations. The
   argument binder rejects an explicitly stored default before execution. *)
Theorem entry_sparse_default_encoding_probe[local]:
  vyper_to_abi FEMPTY (ArrayT (BaseT BoolT) (Fixed 2))
    (ArrayV (SArrayV [(0,BoolV F)])) =
  vyper_to_abi FEMPTY (ArrayT (BaseT BoolT) (Fixed 2))
    (ArrayV (SArrayV [])) /\
  bind_arguments FEMPTY [("a", ArrayT (BaseT BoolT) (Fixed 2))]
    [ArrayV (SArrayV [(0,BoolV F)])] = NONE /\
  IS_SOME (bind_arguments FEMPTY [("a", ArrayT (BaseT BoolT) (Fixed 2))]
    [ArrayV (SArrayV [])])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC
QED
