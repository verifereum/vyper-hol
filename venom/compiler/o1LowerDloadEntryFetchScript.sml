Theory o1LowerDloadEntryFetch
Ancestors
  o1LowerDloadJointEntry analysisSimProofsBase venomExecProofs
  venomWf venomInst venomExecSemantics contextCodegenRel list

Theorem ld_wf_phi_prefix_lt:
  bb_well_formed bb ==>
  phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions
Proof
  strip_tac >> spose_not_then assume_tac >>
  `phi_prefix_length bb.bb_instructions = LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_length_le) >> decide_tac) >>
  mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_no_terminator) >>
  gvs[bb_well_formed_def, EVERY_MEM] >>
  simp[EXISTS_MEM] >> qexists_tac `LAST bb.bb_instructions` >>
  Cases_on `bb.bb_instructions` >> gvs[rich_listTheory.MEM_LAST]
QED

Theorem ld_wf_enters_block_fetch:
  wf_function fn /\ enters_block fn s s1 ==>
  ?bb inst. lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s1.vs_inst_idx = SOME inst /\
    active_inst fn inst s1
Proof
  simp[enters_block_def] >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    metis_tac[ld_wf_phi_prefix_lt] >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qexistsl_tac [`bb`,`EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions`] >>
  simp[get_instruction_def, active_inst_def] >>
  qexists_tac `bb` >> simp[] >> metis_tac[lookup_block_label]
QED
