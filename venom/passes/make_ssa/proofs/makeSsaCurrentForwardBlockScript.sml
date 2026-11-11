Theory makeSsaCurrentForwardBlock
Ancestors
  makeSsaCurrentForwardCut makeSsaCurrentLockstep makeSsaCurrentCutInv
  makeSsaCurrentWfSsa makeSsaCurrentCertificate o1FrameLockstep o1PassLift
  venomExecSemantics venomExecProofs venomExecProps venomWf venomInst
  stateFrame list

Theorem current_cut_exec_block_forward:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  A l = current_block_annotations old pre /\
  LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i <= LENGTH old.bb_instructions /\
  st.vs_current_bb = l /\ st.vs_inst_idx = i /\
  st'.vs_inst_idx = LENGTH pre + i /\
  current_cut_inv fn A renamed H events l i st st' ==>
  case exec_block fuel C old st of
    OK t => ?t'. exec_block fuel C bb' st' = OK t' /\
      current_cut_inv fn A renamed H events l (LENGTH old.bb_instructions) t t'
  | Error e => T
  | r => frame_result_rel r (exec_block fuel C bb' st')
Proof
  map_every qid_spec_tac [`st'`, `st`] >>
  measureInduct_on `LENGTH old.bb_instructions - i` >> rpt gen_tac >> strip_tac >>
  Cases_on `i = LENGTH old.bb_instructions`
  >- simp[Once (cj 2 run_defs), get_instruction_def] >>
  `i < LENGTH old.bb_instructions` by decide_tac >>
  `inst_wf (EL i old.bb_instructions)` by
    metis_tac[current_wf_phi_context_def, fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  drule_all current_cut_inv_ordinary_step_forward >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `bb'' = bb'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bb'' = bb'` SUBST_ALL_TAC >>
  `(EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode =
    (EL i old.bb_instructions).inst_opcode` by fs[inst_pair_def] >>
  `LENGTH pre + i < LENGTH bb'.bb_instructions` by simp[] >>
  once_rewrite_tac[cj 2 run_defs] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel C (EL i old.bb_instructions) st` >>
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[]
  >- suspend "ok"
  >- (strip_tac >> fs[arithmeticTheory.ADD_COMM] >>
      qpat_x_assum `frame_result_rel _ _` mp_tac >>
      qmatch_goalsub_abbrev_tac `frame_result_rel _ r` >>
      Cases_on `r` >> simp[frame_result_rel_def])
  >- (strip_tac >> fs[arithmeticTheory.ADD_COMM] >>
      qpat_x_assum `frame_result_rel _ _` mp_tac >>
      qmatch_goalsub_abbrev_tac `frame_result_rel _ r` >>
      Cases_on `r` >> simp[frame_result_rel_def]) >>
  strip_tac >> fs[arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `frame_result_rel _ _` mp_tac >>
  qmatch_goalsub_abbrev_tac `frame_result_rel _ r` >>
      Cases_on `r` >> simp[frame_result_rel_def]
QED

Resume current_cut_exec_block_forward[ok]:
  strip_tac >> rename1 `step_inst fuel C (EL i old.bb_instructions) st = OK t` >>
  fs[arithmeticTheory.ADD_COMM] >>
  `state_rel (current_cut_sg fn A renamed H events l (SUC i)) t t'` by
    fs[current_cut_inv_def] >>
  `t'.vs_halted = t.vs_halted` by fs[state_rel_def, execution_frame_def] >>
  Cases_on `is_terminator (EL i old.bb_instructions).inst_opcode`
  >- (`bb_well_formed old` by
        metis_tac[current_wf_phi_context_def, wf_function_def, lookup_block_MEM] >>
      `SUC i = LENGTH old.bb_instructions` by
        (fs[bb_well_formed_def] >> metis_tac[arithmeticTheory.SUC_PRE]) >>
      Cases_on `t.vs_halted`
      >- (fs[state_rel_def, execution_frame_def] >> simp[frame_result_rel_def]) >>
      simp[] >> metis_tac[]) >>
  `t.vs_current_bb = l` by metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  simp[] >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`t with vs_inst_idx := SUC i`,
    `t' with vs_inst_idx := SUC (i + LENGTH pre)`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED
Finalise current_cut_exec_block_forward
