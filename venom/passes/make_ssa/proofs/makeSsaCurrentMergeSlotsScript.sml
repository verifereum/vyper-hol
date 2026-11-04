Theory makeSsaCurrentMergeSlots
Ancestors makeSsaCurrentAllocation makeSsaCurrentMergeSeed makeSsaCurrentTokens
  makeSsaCurrentFinalSlots makeSsaCurrentRenameTrace makeSsaCurrentEdgeTrace
  makeSsaCurrentTreeTrace makeSsaCurrentCertificate list

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

Theorem current_tree_trace_nonself_slot:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  lookup_block h bbs = SOME old /\
  ALL_DISTINCT (MAP current_event_label events) /\ MEM ev events /\
  MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss) /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
  i < LENGTH slots /\ EL i slots = (current_event_label ev,v) /\
  current_history_valid V H' /\
  current_env_realizes H' exit_env (current_event_exit_rs ev) V /\ MEM v V /\
  current_token_name H' (CurrentInserted v h) = SOME out /\
  exit_env v <> CurrentInserted v h /\ exit_env v <> CurrentDefault out ==>
  ?new n. lookup_block h bbs' = SOME new /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\
    (EL k new.bb_instructions).inst_opcode = PHI /\
    EL (2*i) (EL k new.bb_instructions).inst_operands = Label (current_event_label ev) /\
    EL (2*i+1) (EL k new.bb_instructions).inst_operands = Var n /\ n <> out
Proof
  strip_tac >>
  `FST (EL i slots) = current_event_label ev` by simp[] >>
  drule_all current_tree_trace_phi_slot >> strip_tac >>
  `current_token_name H' (exit_env v) =
    SOME (latest_current_name (current_event_exit_rs ev) v)` by
    metis_tac[current_env_realizes_def] >>
  drule_all current_inserted_name_separate >> strip_tac >>
  qexistsl_tac [`new`, `latest_current_name (current_event_exit_rs ev) v`] >> simp[]
QED
