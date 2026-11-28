Theory vyperStateCheckpointTest
Ancestors
  vyperStateCheckpoint sptree
Libs
  cv_transLib wordsLib

(* A stale slot must be detected even when the expected sparse support is empty. *)
Theorem checkpoint_extra_storage:
  checkpoint_first_difference T LN
    [((1w,CheckStorage,SOME 1),NumberValue 6382179)] =
  SOME ((1w,CheckStorage,SOME 1),NumberValue 0,NumberValue 6382179)
Proof
  CONV_TAC cv_eval
QED

Theorem checkpoint_missing_transient:
  checkpoint_first_difference F LN
    [((1w,CheckTransient,SOME 7),NumberValue 9)] =
  SOME ((1w,CheckTransient,SOME 7),NumberValue 9,NumberValue 0)
Proof
  CONV_TAC cv_eval
QED

Theorem checkpoint_zero_slots_absent:
  checkpoint_first_difference F LN
    [((1w,CheckStorage,SOME 1),NumberValue 0);
     ((1w,CheckTransient,SOME 2),NumberValue 0)] = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem checkpoint_duplicate_rejected:
  checkpoint_index
    [((1w,CheckBalance,NONE),NumberValue 1);
     ((1w,CheckBalance,NONE),NumberValue 2)] LN = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem checkpoint_log_order:
  (case checkpoint_index
      (checkpoint_log_cells 0 [(1w,[],[2w]);(1w,[],[1w])]) LN of
   | NONE => NONE
   | SOME tree => checkpoint_first_difference F tree
       (checkpoint_log_cells 0 [(1w,[],[1w]);(1w,[],[2w])])) =
  SOME ((1w,CheckData,SOME 0),BytesValue [1w],BytesValue [2w])
Proof
  CONV_TAC cv_eval
QED
