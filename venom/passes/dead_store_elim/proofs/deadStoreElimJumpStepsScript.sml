Theory deadStoreElimJumpSteps
Ancestors
  deadStoreElimLocal deadStoreElimSafety deadStoreElimDefs
  deadStoreElimPending deadStoreElimLiveness deadStoreElimStructure
  venomExecSemantics venomState venomEffects venomInst venomWf
  cfgAnalysisProps cfgHelpers cfgDefs list rich_list basePtrDefs memLocDefs venomExecProps venomExecProofs

Theorem dse_local_agrees_jump_to:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (jump_to lbl s) (jump_to lbl t)
Proof
  strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  simp[jump_to_def, dse_local_agrees_prev_bb,
       dse_local_agrees_current_bb, dse_local_agrees_inst_idx]
QED

Theorem dse_jump_retained:
  inst.inst_opcode IN {JMP; JNZ; DJMP} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def, effects_in_space_def]
QED

Theorem dse_jump_local_step:
  inst.inst_opcode IN {JMP; JNZ; DJMP} /\
  dse_local_agrees sp P s t /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
       dse_local_agrees sp P s1 t1 /\
       s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[dse_safety_agrees_eval_operand]) >>
  fs[] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[dse_local_agrees_jump_to, jump_to_def]
QED

Theorem dse_jump_result_cases:
  inst.inst_opcode IN {JMP; JNZ; DJMP} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "operand operands"] >> simp[]
  >- (Cases_on `operand` >> simp[] >> Cases_on `operands` >> simp[])
  >- (namedCases_on `operands` ["", "second rest"] >> simp[] >>
      Cases_on `second` >> simp[] >>
      namedCases_on `rest` ["", "third tailops"] >> simp[] >>
      Cases_on `third` >> simp[] >> Cases_on `tailops` >> simp[] >>
      Cases_on `eval_operand operand s` >> simp[] >> IF_CASES_TAC >> simp[]) >>
  Cases_on `eval_operand operand s` >> simp[] >>
  Cases_on `extract_labels operands` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem dse_jump_step_successor:
  inst.inst_opcode IN {JMP; JNZ; DJMP} /\
  step_inst fuel ctx inst s = OK s1 ==>
  MEM s1.vs_current_bb (get_successors inst)
Proof
  strip_tac >> fs[] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      AllCaseEqs(), jump_to_def, get_successors_def,
      is_terminator_def, get_label_def]
  >- (IF_CASES_TAC >> simp[])
  >- (IF_CASES_TAC >> simp[]) >>
  drule venomExecProofsTheory.extract_labels_all_labels >> strip_tac >>
  drule_all extract_labels_eq_map >> strip_tac >>
  `MEM (EL (w2n idx) labels) labels` by simp[EL_MEM] >>
  gvs[MEM_MAP, MEM_FILTER, EVERY_MEM] >>
  IF_CASES_TAC >> simp[MEM_FILTER, MEM_MAP] >> metis_tac[]
QED

Theorem dse_jump_final_position:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  get_instruction bb idx = SOME inst /\ inst.inst_opcode IN {JMP; JNZ; DJMP} ==>
  SUC idx = LENGTH bb.bb_instructions /\ LAST bb.bb_instructions = inst
Proof
  strip_tac >> drule_all wf_function_bb_well_formed >>
  simp[bb_well_formed_def] >> strip_tac >>
  `idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `is_terminator inst.inst_opcode` by fs[is_terminator_def] >>
  `idx = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
  conj_tac >- decide_tac >>
  simp[LAST_EL] >> metis_tac[]
QED

Theorem dse_jump_cfg_successor:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  get_instruction bb idx = SOME inst /\ inst.inst_opcode IN {JMP; JNZ; DJMP} /\
  step_inst fuel ctx inst s = OK s1 ==>
  SUC idx = LENGTH bb.bb_instructions /\
  MEM s1.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)
Proof
  strip_tac >> drule_all dse_jump_final_position >> strip_tac >> simp[] >>
  `cfg_succs_of (cfg_analyze fn) bb.bb_label = bb_succs bb` by
    (rewrite_tac[cfg_analyze_succs] >> irule cfg_succs_of_build_succs >>
     fs[wf_function_def, fn_labels_def]) >>
  drule_all dse_jump_step_successor >>
  Cases_on `bb.bb_instructions` >> gvs[bb_succs_def]
QED

Theorem dse_jump_no_clobber:
  inst.inst_opcode IN {JMP; JNZ; DJMP} /\ loc.ml_size <> SOME 0 ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> Cases_on `sp` >> fs[] >>
  simp[dse_inst_clobbers_def, bp_get_write_location_def,
       is_raw_fmp_opcode_def, write_effects_def, empty_effects_def,
       ml_is_fixed_def, completely_contains_def, ml_empty_def] >>
  Cases_on `loc.ml_offset` >> Cases_on `loc.ml_size` >> gvs[]
QED

Theorem dse_pending_at_successor:
  wf_function fn /\ MEM bb1 fn.fn_blocks /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  LENGTH bb.bb_instructions <= idx /\
  MEM bb1.bb_label (cfg_succs_of cfg bb.bb_label) ==>
  dse_pending_at cfg bp sp fn bb1 0 P s
Proof
  strip_tac >> rewrite_tac[dse_pending_at_def] >>
  reverse conj_tac >- fs[dse_pending_at_def] >>
  simp[EVERY_MEM] >> qx_gen_tac `entry` >> strip_tac >>
  PairCases_on `entry` >> drule_all dse_pending_at_member >> strip_tac >>
  simp[] >> irule dse_label_dead_suffix >> simp[] >>
  irule dse_suffix_dead_successor >> metis_tac[]
QED

Theorem dse_jump_pending_step:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  inst.inst_opcode IN {JMP; JNZ; DJMP} /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  dse_pending_at (cfg_analyze fn) bp sp fn bb s.vs_inst_idx P s /\
  step_inst fuel ctx inst s = OK s1 /\ s1.vs_allocas = s.vs_allocas /\
  lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb1 ==>
  dse_pending_at (cfg_analyze fn) bp sp fn bb1 0 P s1
Proof
  strip_tac >> drule_all dse_jump_cfg_successor >> strip_tac >>
  `MEM bb1 fn.fn_blocks /\ bb1.bb_label = s1.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  irule dse_pending_at_allocas_extend >> qexists_tac `s` >> simp[] >>
  irule dse_pending_at_successor >> simp[] >>
  qexistsl_tac [`bb`, `SUC s.vs_inst_idx`] >> simp[] >>
  qpat_x_assum `SUC _ = LENGTH _` (fn th => rewrite_tac[GSYM th]) >>
  irule dse_pending_at_step >> simp[] >> rpt strip_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  `loc.ml_size <> SOME 0` by simp[] >>
  `~dse_inst_clobbers bp sp loc inst` by
    (irule dse_jump_no_clobber >> simp[]) >>
  gvs[get_instruction_def, AllCaseEqs()]
QED

Theorem dse_jump_step:
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  wf_function fn /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  dse_local_agrees sp P s t /\
  dse_pending_at (cfg_analyze fn) bp sp fn bb s.vs_inst_idx P s /\
  inst.inst_opcode IN {JMP; JNZ; DJMP} /\
  step_inst fuel ctx inst s = OK s1 /\
  lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb1 ==>
  ?t1. step_inst fuel ctx (dse_inst ids sp inst) t = OK t1 /\
    dse_local_agrees sp P s1 t1 /\
    dse_pending_at (cfg_analyze fn) bp sp fn bb1 0 P s1
Proof
  strip_tac >> drule_all dse_jump_local_step >> strip_tac >>
  drule_all dse_jump_retained >> disch_then (qspec_then `ids` SUBST1_TAC) >>
  qexists_tac `t1` >> simp[] >> irule dse_jump_pending_step >>
  rpt (goal_assum (drule_at Any)) >> metis_tac[lookup_block_MEM]
QED
