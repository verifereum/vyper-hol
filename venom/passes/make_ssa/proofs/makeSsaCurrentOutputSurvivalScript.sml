Theory makeSsaCurrentOutputSurvival
Ancestors
  makeSsaCurrentWfSsa makeSsaCurrentDefs venomInst venomExecProofs list pred_set

Theorem current_reassign_output_set:
  !ids xs. set (FLAT (MAP instruction_inst_outputs
    (reassign_current_inst_ids ids xs))) =
    set (FLAT (MAP instruction_inst_outputs xs))
Proof
  Induct >> Cases_on `xs` >> simp[reassign_current_inst_ids_def]
QED

Theorem current_cleanup_parts_output_set:
  !xs phis ord.
  (!i. MEM i xs /\ i.inst_opcode = PHI ==>
    (simplify_current_phi i).inst_outputs = i.inst_outputs) /\
  simplify_current_phi_prefix_parts xs = (phis,ord) ==>
  set (FLAT (MAP instruction_inst_outputs (phis ++ ord))) =
  set (FLAT (MAP instruction_inst_outputs xs))
Proof
  Induct >- simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode <> PHI`
  >- gvs[simplify_current_phi_prefix_parts_def] >>
  Cases_on `simplify_current_phi_prefix_parts xs` >>
  `set (FLAT (MAP instruction_inst_outputs (q ++ r))) =
   set (FLAT (MAP instruction_inst_outputs xs))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `(simplify_current_phi h).inst_outputs = h.inst_outputs` by metis_tac[MEM] >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
  gvs[simplify_current_phi_prefix_parts_def, MAP_APPEND, FLAT_APPEND] >>
  ASM_SET_TAC[]
QED

Theorem current_context_phi_outputs:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ MEM i new.bb_instructions /\
  i.inst_opcode = PHI ==>
  (simplify_current_phi i).inst_outputs = i.inst_outputs
Proof
  strip_tac >>
  `?q. q < LENGTH new.bb_instructions /\ i = EL q new.bb_instructions` by
    metis_tac[MEM_EL] >> gvs[] >>
  drule_all current_wf_phi_occurrence_cleanup_cases >>
  rpt strip_tac >> simp[]
QED

Theorem current_context_block_output_set:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new ==>
  set (FLAT (MAP instruction_inst_outputs
    (simplify_current_phi_block new).bb_instructions)) =
  set (FLAT (MAP instruction_inst_outputs new.bb_instructions))
Proof
  strip_tac >>
  `!i. MEM i new.bb_instructions /\ i.inst_opcode = PHI ==>
    (simplify_current_phi i).inst_outputs = i.inst_outputs` by
    metis_tac[current_context_phi_outputs] >>
  Cases_on `new.bb_instructions` >- simp[simplify_current_phi_block_def] >>
  simp[simplify_current_phi_block_def] >>
  Cases_on `h'.inst_opcode = PHI` >> simp[] >>
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >>
  simp[current_reassign_output_set] >>
  drule current_cleanup_parts_output_set >> simp[] >> metis_tac[]
QED

Theorem current_context_cleanup_producer:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ MEM i new.bb_instructions /\
  MEM x i.inst_outputs ==>
  ?j. MEM j (simplify_current_phi_block new).bb_instructions /\
    MEM x j.inst_outputs
Proof
  strip_tac >> drule_all current_context_block_output_set >>
  simp[EXTENSION, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_context_conditional_producer:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ MEM i new.bb_instructions /\
  MEM x i.inst_outputs ==>
  ?b j. MEM b (simplify_current_phis_if enabled renamed) /\
    b.bb_label = new.bb_label /\ MEM j b.bb_instructions /\ MEM x j.inst_outputs
Proof
  strip_tac >>
  `MEM new renamed` by metis_tac[lookup_block_MEM] >>
  Cases_on `enabled /\ blocks_have_leading_phi renamed`
  >- (qexists `simplify_current_phi_block new` >>
      gvs[simplify_current_phis_if_def, simplify_current_phis_def] >>
      `MEM (simplify_current_phi_block new) (MAP simplify_current_phi_block renamed)` by
        (simp[MEM_MAP] >> metis_tac[]) >>
      metis_tac[current_context_cleanup_producer]) >>
  `simplify_current_phis_if enabled renamed = renamed` by
    (Cases_on `enabled` >> gvs[simplify_current_phis_if_def, simplify_current_phis_def]) >>
  qexistsl [`new`, `i`] >> simp[]
QED
