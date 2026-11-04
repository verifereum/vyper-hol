Theory makeSsaCurrentMergeSlots
Ancestors makeSsaCurrentAllocation makeSsaCurrentMergeSeed makeSsaCurrentTokens

Theorem current_inserted_name_collision:
  current_history_valid V H /\
  current_token_name H (CurrentInserted v h) = SOME out /\
  current_token_name H t = SOME n ==>
  (n = out <=> t = CurrentInserted v h \/ t = CurrentDefault out)
Proof
  strip_tac >> Cases_on `?w. t = CurrentDefault w`
  >- gvs[] >>
  eq_tac
  >- (strip_tac >> gvs[] >>
      irule current_allocated_name_injective >>
      goal_assum $ drule_at Any >> simp[] >> metis_tac[]) >>
  strip_tac >> gvs[]
QED

Theorem current_inserted_name_separate:
  current_history_valid V H /\
  current_token_name H (CurrentInserted v h) = SOME out /\
  current_token_name H t = SOME n /\
  t <> CurrentInserted v h /\ t <> CurrentDefault out ==>
  n <> out
Proof
  metis_tac[current_inserted_name_collision]
QED
