Theory makeSsaCurrentFinalSlots
Ancestors
  makeSsaCurrentTreePaths makeSsaCurrentTreeTrace makeSsaCurrentEdgeTrace
  makeSsaCurrentRenameTrace makeSsaCurrentInduct makeSsaDefs
   cfgTransformProps venomInst list rich_list pair
  venomExecProofs

Definition current_phi_view_def:
  current_phi_view insts =
    MAP (\inst. if inst.inst_opcode = PHI then SOME inst.inst_operands else NONE) insts
End

Definition current_event_slot_action_def:
  current_event_slot_action sm h ev view =
    if MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss)
    then MAP (OPTION_MAP (update_current_phi_for_pred
      (current_event_exit_rs ev) (current_event_label ev))) view
    else view
End

Theorem current_inst_trace_phi_view:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  (if inst'.inst_opcode = PHI then SOME inst'.inst_operands else NONE) =
  (if inst.inst_opcode = PHI then SOME inst.inst_operands else NONE)
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem current_local_trace_phi_view:
  !annss insts s rs H E insts' s' rs' H' E'.
    current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
    current_phi_view insts' = current_phi_view insts
Proof
  Induct >> simp[current_local_trace_def, current_phi_view_def] >>
  rpt strip_tac >>
  drule current_inst_trace_phi_view >> strip_tac >>
  first_x_assum drule >> simp[current_phi_view_def]
QED

Theorem current_edge_block_phi_view:
  current_phi_view (current_edge_block rs p bb).bb_instructions =
  MAP (OPTION_MAP (update_current_phi_for_pred rs p)) (current_phi_view bb.bb_instructions)
Proof
  simp[current_phi_view_def, current_edge_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[current_edge_inst_def] >> rpt strip_tac >>
  Cases_on `x.inst_opcode = PHI` >> simp[]
QED

Theorem current_succ_phis_phi_view:
  ALL_DISTINCT succs /\ lookup_block h bbs = SOME old ==>
  ?new. lookup_block h (update_current_succ_phis rs p bbs succs) = SOME new /\
    current_phi_view new.bb_instructions =
      if MEM h succs then MAP (OPTION_MAP (update_current_phi_for_pred rs p))
        (current_phi_view old.bb_instructions) else current_phi_view old.bb_instructions
Proof
  strip_tac >> drule current_succ_phis_lookup >>
  disch_then (qspecl_then [`bbs`,`h`,`rs`,`p`] mp_tac) >>
  simp[] >> strip_tac >> Cases_on `MEM h succs` >>
  simp[current_edge_block_phi_view]
QED

Definition current_blocks_phi_view_def:
  current_blocks_phi_view bbs h =
    OPTION_MAP (\bb. current_phi_view bb.bb_instructions) (lookup_block h bbs)
End

Theorem current_replace_phi_view:
  lookup_block l bbs = SOME bb /\ current_phi_view insts = current_phi_view bb.bb_instructions ==>
  current_blocks_phi_view (replace_block l (bb with bb_instructions := insts) bbs) h =
    current_blocks_phi_view bbs h
Proof
  strip_tac >> drule lookup_block_label >> strip_tac >>
  simp[current_blocks_phi_view_def] >> Cases_on `h = l` >> gvs[]
  >- (qexists_tac `bb with bb_instructions := insts` >> simp[] >>
      irule lookup_block_replace_eq >> simp[]) >>
  simp[lookup_block_replace_neq]
QED

Theorem current_succ_phis_blocks_view:
  ALL_DISTINCT succs ==>
  current_blocks_phi_view (update_current_succ_phis rs p bbs succs) h =
    OPTION_MAP (\view. if MEM h succs then
      MAP (OPTION_MAP (update_current_phi_for_pred rs p)) view else view)
      (current_blocks_phi_view bbs h)
Proof
  strip_tac >> drule current_succ_phis_lookup >>
  disch_then (qspecl_then [`bbs`,`h`,`rs`,`p`] mp_tac) >>
  strip_tac >> simp[current_blocks_phi_view_def] >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  Cases_on `MEM h succs` >> simp[current_edge_block_phi_view]
QED

Theorem current_view_fold_append:
  OPTION_MAP (\view. FOLDL f view ys)
    (OPTION_MAP (\view. FOLDL f view xs) opt) =
  OPTION_MAP (\view. FOLDL f view (xs ++ ys)) opt
Proof
  Cases_on `opt` >> simp[FOLDL_APPEND]
QED

Theorem current_tree_trace_phi_view:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) ==>
    !h. current_blocks_phi_view bbs' h =
      OPTION_MAP (\view. FOLDL (\view ev. current_event_slot_action sm h ev view)
        view events) (current_blocks_phi_view bbs h)) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) ==>
    !h. current_blocks_phi_view bbs' h =
      OPTION_MAP (\view. FOLDL (\view ev. current_event_slot_action sm h ev view)
        view events) (current_blocks_phi_view bbs h))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs`
      >- (simp[] >> rpt strip_tac >>
          Cases_on `current_blocks_phi_view bbs h` >> simp[]) >>
      simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_phi_view >> strip_tac >>
      qmatch_asmsub_abbrev_tac `update_current_succ_phis rs1 lbl changed succs` >>
      `ALL_DISTINCT succs` by
        (simp[Abbr `succs`] >> Cases_on `ALOOKUP sm lbl` >> gvs[] >> metis_tac[]) >>
      `!h. current_blocks_phi_view changed h = current_blocks_phi_view bbs h` by
        (gen_tac >> simp[Abbr `changed`] >> irule current_replace_phi_view >> simp[]) >>
      first_x_assum drule_all >> strip_tac >> gen_tac >>
      first_x_assum (qspec_then `h` mp_tac) >>
      simp[current_succ_phis_blocks_view, current_event_slot_action_def,
        current_event_label_def, current_event_exit_rs_def] >>
      Cases_on `current_blocks_phi_view bbs h` >> simp[])
  >- (simp[current_tree_trace_def] >> rpt strip_tac >>
      Cases_on `current_blocks_phi_view bbs h` >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  last_x_assum drule_all >> strip_tac >>
  last_x_assum drule_all >> strip_tac >>
  simp[current_view_fold_append]
QED

Theorem current_tree_trace_phi_lookup:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  lookup_block h bbs = SOME old ==>
  ?new. lookup_block h bbs' = SOME new /\
    current_phi_view new.bb_instructions =
      FOLDL (\view ev. current_event_slot_action sm h ev view)
        (current_phi_view old.bb_instructions) events
Proof
  strip_tac >> drule_all (cj 1 current_tree_trace_phi_view) >>
  disch_then (qspec_then `h` mp_tac) >>
  simp[current_blocks_phi_view_def] >>
  Cases_on `lookup_block h bbs'` >> simp[]
QED

Definition current_event_operand_action_def:
  current_event_operand_action sm h ev ops =
    if MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss)
    then update_current_phi_for_pred (current_event_exit_rs ev) (current_event_label ev) ops
    else ops
End

Definition current_event_pair_action_def:
  current_event_pair_action sm h ev slot =
    (FST slot,
      if MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss) /\
         FST slot = current_event_label ev
      then latest_current_name (current_event_exit_rs ev) (SND slot)
      else SND slot)
End

Theorem current_event_operand_slots:
  current_event_operand_action sm h ev (current_phi_slots slots) =
  current_phi_slots (MAP (current_event_pair_action sm h ev) slots)
Proof
  rewrite_tac[current_event_operand_action_def, current_event_pair_action_def] >>
  IF_CASES_TAC
  >- (simp[current_phi_slots_update] >> AP_TERM_TAC >>
      irule MAP_CONG >> simp[] >> rpt strip_tac >> Cases_on `x` >>
      simp[current_event_pair_action_def]) >>
  `current_event_pair_action sm h ev = I` by
    (simp[FUN_EQ_THM, current_event_pair_action_def] >> Cases >> simp[]) >>
  simp[]
QED

Theorem current_event_pair_fst[simp]:
  FST (current_event_pair_action sm h ev slot) = FST slot
Proof
  simp[current_event_pair_action_def]
QED

Theorem current_event_fold_slots:
  !events slots.
  FOLDL (\ops ev. current_event_operand_action sm h ev ops)
    (current_phi_slots slots) events =
  current_phi_slots (MAP (\slot. FOLDL (\slot ev. current_event_pair_action sm h ev slot)
    slot events) slots)
Proof
  Induct >> simp[current_event_operand_slots] >>
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem current_event_fold_pair_fst[simp]:
  !events slot.
  FST (FOLDL (\slot ev. current_event_pair_action sm h ev slot) slot events) = FST slot
Proof
  Induct >> simp[]
QED

Theorem current_event_fold_pair_absent:
  !events slot.
  ~MEM (FST slot) (MAP current_event_label events) ==>
  FOLDL (\slot ev. current_event_pair_action sm h ev slot) slot events = slot
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `current_event_pair_action sm h h' slot = slot` by
    (Cases_on `slot` >> fs[current_event_pair_action_def] >> metis_tac[]) >>
  simp[]
QED

Theorem current_event_fold_pair_unique:
  !events slot ev.
  ALL_DISTINCT (MAP current_event_label events) /\ MEM ev events /\
  FST slot = current_event_label ev /\
  MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss) ==>
  FOLDL (\slot ev. current_event_pair_action sm h ev slot) slot events =
    (FST slot, latest_current_name (current_event_exit_rs ev) (SND slot))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `h' = ev`
  >- (qpat_x_assum `!slot ev. _` kall_tac >>
      qpat_x_assum `h' = ev` SUBST_ALL_TAC >>
      rewrite_tac[current_event_fold_pair_absent] >>
      `~MEM (FST (current_event_pair_action sm h ev slot))
        (MAP current_event_label events)` by simp[] >>
      drule current_event_fold_pair_absent >> simp[current_event_pair_action_def]) >>
  `MEM ev events` by metis_tac[] >>
  `current_event_label h' <> current_event_label ev` by
    (gvs[MEM_MAP] >> metis_tac[]) >>
  `current_event_pair_action sm h h' slot = slot` by
    (Cases_on `slot` >> fs[current_event_pair_action_def] >> metis_tac[]) >>
  fs[] >> metis_tac[]
QED

Theorem current_option_map_identity[simp]:
  OPTION_MAP (\x:'a. x) = I
Proof
  simp[FUN_EQ_THM] >> Cases >> simp[]
QED

Theorem current_event_view_fold:
  !events view.
  FOLDL (\view ev. current_event_slot_action sm h ev view) view events =
  MAP (OPTION_MAP (\ops. FOLDL (\ops ev. current_event_operand_action sm h ev ops)
    ops events)) view
Proof
  Induct
  >- simp[] >>
  simp[current_event_slot_action_def, current_event_operand_action_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> Cases >> simp[]
QED

Theorem current_event_fold_slots_index:
  ALL_DISTINCT (MAP current_event_label events) /\ MEM ev events /\
  MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss) /\
  i < LENGTH slots /\ FST (EL i slots) = current_event_label ev ==>
  EL (2 * i) (FOLDL (\ops ev. current_event_operand_action sm h ev ops)
    (current_phi_slots slots) events) = Label (current_event_label ev) /\
  EL (2 * i + 1) (FOLDL (\ops ev. current_event_operand_action sm h ev ops)
    (current_phi_slots slots) events) =
      Var (latest_current_name (current_event_exit_rs ev) (SND (EL i slots)))
Proof
  strip_tac >> rewrite_tac[current_event_fold_slots] >>
  qspec_then `MAP (\slot. FOLDL (\slot ev. current_event_pair_action sm h ev slot)
    slot events) slots` (qspec_then `i` mp_tac) current_phi_slots_index >>
  simp[EL_MAP] >>
  drule_all current_event_fold_pair_unique >> simp[]
QED

Theorem current_phi_view_length[simp]:
  LENGTH (current_phi_view insts) = LENGTH insts
Proof
  simp[current_phi_view_def]
QED

Theorem current_phi_view_fold_instruction:
  current_phi_view insts' =
    FOLDL (\view ev. current_event_slot_action sm h ev view)
      (current_phi_view insts) events /\
  k < LENGTH insts /\ (EL k insts).inst_opcode = PHI ==>
  LENGTH insts' = LENGTH insts /\
  k < LENGTH insts' /\ (EL k insts').inst_opcode = PHI /\
  (EL k insts').inst_operands =
    FOLDL (\ops ev. current_event_operand_action sm h ev ops)
      (EL k insts).inst_operands events
Proof
  rewrite_tac[current_event_view_fold] >> strip_tac >>
  `LENGTH insts' = LENGTH insts` by
    metis_tac[LENGTH_MAP, current_phi_view_length] >>
  `EL k (current_phi_view insts') =
    SOME (FOLDL (\ops ev. current_event_operand_action sm h ev ops)
      (EL k insts).inst_operands events)` by
    (simp[EL_MAP, current_phi_view_def]) >>
  qpat_x_assum `current_phi_view insts' = _` kall_tac >>
  `k < LENGTH insts'` by simp[] >>
  fs[current_phi_view_def, EL_MAP] >>
  Cases_on `(EL k insts').inst_opcode = PHI` >> gvs[]
QED

Theorem current_tree_trace_phi_slot:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  lookup_block h bbs = SOME old /\
  ALL_DISTINCT (MAP current_event_label events) /\ MEM ev events /\
  MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss) /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
  i < LENGTH slots /\ FST (EL i slots) = current_event_label ev ==>
  ?new. lookup_block h bbs' = SOME new /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\
    (EL k new.bb_instructions).inst_opcode = PHI /\
    EL (2 * i) (EL k new.bb_instructions).inst_operands = Label (current_event_label ev) /\
    EL (2 * i + 1) (EL k new.bb_instructions).inst_operands =
      Var (latest_current_name (current_event_exit_rs ev) (SND (EL i slots)))
Proof
  strip_tac >> drule_all current_tree_trace_phi_lookup >> strip_tac >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  qexists_tac `new` >> simp[] >>
  irule current_event_fold_slots_index >> simp[]
QED
