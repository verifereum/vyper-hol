Theory makeSsaCurrentActualEdgeValues
Ancestors
  makeSsaCurrentFinalSlots makeSsaCurrentPhiRuntime makeSsaCurrentAllocation
  makeSsaCurrentTreeTrace makeSsaCurrentEdgeTrace makeSsaCurrentTokens
  makeSsaCurrentDefs venomState venomInst list pair

Theorem current_actual_edge_slot_value:
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
  current_env_realizes H' exit_env (current_event_exit_rs ev) V /\
  current_token_values H' exit_env demands source incoming /\
  MEM v V /\ MEM v demands ==>
  ?new n. lookup_block h bbs' = SOME new /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\
    (EL k new.bb_instructions).inst_opcode = PHI /\
    EL (2 * i) (EL k new.bb_instructions).inst_operands = Label (current_event_label ev) /\
    EL (2 * i + 1) (EL k new.bb_instructions).inst_operands = Var n /\
    lookup_var n incoming = lookup_var v source
Proof
  strip_tac >>
  `FST (EL i slots) = current_event_label ev` by simp[] >>
  drule_all current_tree_trace_phi_slot >> strip_tac >>
  qexistsl_tac [`new`, `latest_current_name (current_event_exit_rs ev) v`] >>
  asm_rewrite_tac[] >>
  `current_token_name H' (exit_env v) =
    SOME (latest_current_name (current_event_exit_rs ev) v)` by
    metis_tac[current_env_realizes_def] >>
  gvs[] >> metis_tac[current_token_values_lookup]
QED

Theorem current_actual_edge_slot_defined:
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
  current_env_realizes H' exit_env (current_event_exit_rs ev) V /\
  current_token_values H' exit_env demands source incoming /\
  MEM v V /\ MEM v demands /\ lookup_var v source = SOME value ==>
  ?new n. lookup_block h bbs' = SOME new /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\
    (EL k new.bb_instructions).inst_opcode = PHI /\
    EL (2 * i) (EL k new.bb_instructions).inst_operands = Label (current_event_label ev) /\
    EL (2 * i + 1) (EL k new.bb_instructions).inst_operands = Var n /\
    lookup_var n incoming = SOME value
Proof
  strip_tac >> drule_all current_actual_edge_slot_value >>
  strip_tac >> qexistsl_tac [`new`, `n`] >> simp[]
QED
