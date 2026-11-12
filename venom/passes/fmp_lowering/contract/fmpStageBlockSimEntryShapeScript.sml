Theory fmpStageBlockSimEntryShape
Ancestors
  fmpStageControl fmpStageOpBase venomExecProofs venomWfProps
  cfgWf cfgHelpers livenessProofs fmpStepRewrite
  venomExecSemantics venomState venomInst frameCfgBoundary list

Theorem fmp_entry_jump_successor:
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst k C bi s = OK (jump_to lbl s) ==>
  MEM lbl (get_successors bi)
Proof
  strip_tac >>
  `bi.inst_opcode <> INVOKE` by gvs[] >>
  gvs[step_inst_non_invoke] >>
  gvs[step_inst_base_def, get_successors_def, AllCaseEqs(),
      jump_to_def] >>
  first_x_assum (mp_tac o AP_TERM ``\s:venom_state. s.vs_current_bb``) >>
  simp[] >> strip_tac >>
  gvs[is_terminator_def, get_label_def] >>
  all_tac
  >- (IF_CASES_TAC >> simp[])
  >- (IF_CASES_TAC >> simp[]) >>
  drule extract_labels_filtered >> strip_tac >>
  IF_CASES_TAC >> simp[] >> metis_tac[EL_MEM]
QED

Theorem fmp_entry_jump_edge:
  wf_function fn /\ first_block_no_preds fn /\ active_inst fn bi s /\
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst k C bi s = OK (jump_to lbl s) ==>
  ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    SUC s.vs_inst_idx = LENGTH bb.bb_instructions /\
    MEM lbl (bb_succs bb) /\
    fn_cfg_edge fn s.vs_current_bb lbl /\
    lbl <> (HD fn.fn_blocks).bb_label
Proof
  strip_tac >> drule_all fmp_entry_jump_successor >> strip_tac >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[contextCodegenRelTheory.active_inst_def] >> strip_tac >>
  `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
  `is_terminator bi.inst_opcode` by gvs[is_terminator_def] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[venomWfTheory.bb_well_formed_def] >>
  `bi = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[LAST_EL]) >>
  `MEM lbl (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub, MEM_REVERSE]) >>
  qexists_tac `bb` >> simp[] >>
  conj_tac
  >- (irule MEM_lookup_block >>
      gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  conj_tac >- (simp[venomWfTheory.fn_cfg_edge_def] >> metis_tac[]) >>
  gvs[unitShapeDefsTheory.first_block_no_preds_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem fmp_entry_indexed_phis:
  !insts k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\
  (!n base. n < phi_prefix_length insts ==>
    ~MEM ((label,k+n),base) restores) ==>
  collect_phis out = collect_phis insts /\
  phi_prefix_length out = phi_prefix_length insts
Proof
  Induct
  >- simp[fmpLowerDefsTheory.fmp_lower_indexed_def,
          livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
  rpt gen_tac >>
  simp[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons] >>
  strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`bases = []` by
        (drule fmpLowerIndexedPropsTheory.fmp_select_point_restores_once >> strip_tac >>
         qpat_x_assum `!n base. _` (qspec_then `0` mp_tac) >>
         simp[phi_prefix_length_def] >>
         Cases_on `bases` >> gvs[] >> metis_tac[]) >>
      gvs[fmpLowerDefsTheory.fmp_emit_restores_def] >>
      drule fmp_lower_inst_phi >> simp[] >> strip_tac >> gvs[] >>
      simp[livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
      first_x_assum irule >> goal_assum (drule_at Any) >>
      rpt strip_tac >>
      drule fmpLowerIndexedPropsTheory.fmp_select_point_restores_once >> strip_tac >>
      qpat_x_assum `!n base. _` (qspec_then `SUC n` mp_tac) >>
      gvs[phi_prefix_length_def, arithmeticTheory.ADD_CLAUSES,
          arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  drule fmp_lower_inst_phi >> simp[] >> strip_tac >>
  drule fmp_lower_inst_terminal >> strip_tac >>
  drule fmp_emit_restores_not_phi >> strip_tac >>
  Cases_on `prefix` >> Cases_on `head` >>
  gvs[livenessDefsTheory.collect_phis_def, phi_prefix_length_def]
QED
