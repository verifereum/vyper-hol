Theory makeSsaCurrentSelectedEdge
Ancestors makeSsaCurrentFinalSlots makeSsaCurrentPhiRuntime list

Theorem current_event_fold_find[local]:
  !slots. ALL_DISTINCT (MAP current_event_label events) /\ MEM ev events /\
  MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss) ==>
  OPTION_MAP (Var o SND)
    (FIND (\slot. FST slot = current_event_label ev)
      (MAP (\slot. FOLDL (\slot e. current_event_pair_action sm h e slot)
         slot events) slots)) =
  OPTION_MAP (\slot. Var (latest_current_name (current_event_exit_rs ev) (SND slot)))
    (FIND (\slot. FST slot = current_event_label ev) slots)
Proof
  Induct >> simp[FIND_thm] >> rpt strip_tac >>
  Cases_on `FST h' = current_event_label ev` >> simp[] >>
  drule_all current_event_fold_pair_unique >> simp[]
QED

Theorem current_event_fold_resolve:
  ALL_DISTINCT (MAP current_event_label events) /\ MEM ev events /\
  MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss) ==>
  resolve_phi (current_event_label ev)
    (FOLDL (\ops e. current_event_operand_action sm h e ops)
      (current_phi_slots slots) events) =
  OPTION_MAP (\slot. Var (latest_current_name (current_event_exit_rs ev) (SND slot)))
    (FIND (\slot. FST slot = current_event_label ev) slots)
Proof
  simp[current_event_fold_slots, current_resolve_phi_slots,
       current_event_fold_find]
QED

Theorem current_tree_trace_phi_resolve:
  current_tree_trace A sm tree s rs bbs H E visited ctrs' s' bbs' H' visited' events /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  lookup_block h bbs = SOME old /\
  ALL_DISTINCT (MAP current_event_label events) /\ MEM ev events /\
  MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss) /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots ==>
  ?new. lookup_block h bbs' = SOME new /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\
    (EL k new.bb_instructions).inst_opcode = PHI /\
    resolve_phi (current_event_label ev) (EL k new.bb_instructions).inst_operands =
    OPTION_MAP (\slot. Var (latest_current_name (current_event_exit_rs ev) (SND slot)))
      (FIND (\slot. FST slot = current_event_label ev) slots)
Proof
  strip_tac >> drule_all current_tree_trace_phi_lookup >> strip_tac >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  qexists_tac `new` >> simp[current_event_fold_resolve]
QED
