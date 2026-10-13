(* Regression: storage and transient dynamic-array pop writes only the header.
   Nonzero inactive slots deliberately remain present, including on empty pop. *)
Theory vyperStoragePopTest
Ancestors
  vyperSmallStep vyperStorageBackend
Libs
  cv_transLib wordsLib finite_mapLib

Definition pop_test_context_def:
  pop_test_context b = empty_evaluation_context with
    <| sources := [(0w, [(NONE,
         [VariableDecl Private (if b then Transient else Storage) "items"
           (ArrayT (BaseT (UintT 8)) (Dynamic 4)) (SOME 4)])])];
       layouts := [(0w, ([((NONE,"items"),4)], [((NONE,"items"),4)]))] |>
End
val () = cv_auto_trans pop_test_context_def;

Definition pop_test_state_def:
  pop_test_state b len = SND (set_storage_backend (pop_test_context b) b
    (update_storage 4w (n2w len) (update_storage 5w 11w
      (update_storage 6w 37w (update_storage 20w 73w empty_storage))))
    empty_state)
End
val () = cv_auto_trans pop_test_state_def;

(* Exact state equality checks the single write and frames the other backend,
   logs, scopes, accounts/immutables, and all non-header slots. *)
Theorem storage_pop_nonzero_slot_retained:
  assign_target (pop_test_context F)
    (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state F 2) =
    (INL (SOME (IntV 37)),
     SND (write_storage_slot (pop_test_context F) F 4w (BaseTV (UintT 256))
       (IntV 1) (pop_test_state F 2))) /\
  lookup_storage 6w (get_storage (pop_test_context F)
    (SND (assign_target (pop_test_context F)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state F 2))) F) = 37w /\
  lookup_storage 4w (get_storage (pop_test_context F)
    (SND (assign_target (pop_test_context F)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state F 2))) F) = 1w
Proof
  EVAL_TAC >> simp[]
QED

Theorem transient_pop_nonzero_slot_retained:
  assign_target (pop_test_context T)
    (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state T 2) =
    (INL (SOME (IntV 37)),
     SND (write_storage_slot (pop_test_context T) T 4w (BaseTV (UintT 256))
       (IntV 1) (pop_test_state T 2))) /\
  lookup_storage 6w (get_storage (pop_test_context T)
    (SND (assign_target (pop_test_context T)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state T 2))) T) = 37w /\
  lookup_storage 4w (get_storage (pop_test_context T)
    (SND (assign_target (pop_test_context T)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state T 2))) T) = 1w
Proof
  EVAL_TAC >> simp[]
QED

(* Exercise the translated assign_target implementation as well as EVAL. *)
Theorem storage_pop_cv_result:
  FST (assign_target (pop_test_context F)
    (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state F 2)) =
  INL (SOME (IntV 37))
Proof
  CONV_TAC cv_eval
QED

Theorem transient_pop_cv_result:
  FST (assign_target (pop_test_context T)
    (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state T 2)) =
  INL (SOME (IntV 37))
Proof
  CONV_TAC cv_eval
QED

Theorem storage_pop_cv_slots:
  FST (read_storage_slot (pop_test_context F) F 6w (BaseTV (UintT 8))
    (SND (assign_target (pop_test_context F)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state F 2)))) =
    INL (IntV 37) /\
  FST (read_storage_slot (pop_test_context F) F 4w (BaseTV (UintT 256))
    (SND (assign_target (pop_test_context F)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state F 2)))) =
    INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

Theorem transient_pop_cv_slots:
  FST (read_storage_slot (pop_test_context T) T 6w (BaseTV (UintT 8))
    (SND (assign_target (pop_test_context T)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state T 2)))) =
    INL (IntV 37) /\
  FST (read_storage_slot (pop_test_context T) T 4w (BaseTV (UintT 256))
    (SND (assign_target (pop_test_context T)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state T 2)))) =
    INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

Theorem storage_pop_empty_unchanged:
  assign_target (pop_test_context F)
    (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state F 0) =
    (INR (Error (RuntimeError "pop empty storage array")),pop_test_state F 0)
Proof
  EVAL_TAC
QED

Theorem transient_pop_empty_unchanged:
  assign_target (pop_test_context T)
    (BaseTargetV (TopLevelVar NONE "items") []) PopOp (pop_test_state T 0) =
    (INR (Error (RuntimeError "pop empty storage array")),pop_test_state T 0)
Proof
  EVAL_TAC
QED
