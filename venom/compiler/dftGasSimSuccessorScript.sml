Theory dftGasSimSuccessor
Ancestors
  dftGasSimEndpoint dftGasOracleDefs venomExecProofs venomExecSemantics
  venomWf venomInst venomState list pred_set

Theorem ev_block_current_bb_in_succs:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  s.vs_inst_idx <= LENGTH bb.bb_instructions /\
  ev_block orc p d fuel C bb s = OK t ==>
  MEM t.vs_current_bb (bb_succs bb)
Proof
  strip_tac >>
  `!n fuel C s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     ev_block orc p d fuel C bb s = OK t ==>
     MEM t.vs_current_bb (bb_succs bb)` suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `s'.vs_inst_idx >= LENGTH bb.bb_instructions`
  >- (qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once ev_block_def, get_instruction_def]) >>
  qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[ev_block_def] >> simp[get_instruction_def] >>
  Cases_on `ev_step orc p d fuel' C' (EL s'.vs_inst_idx bb.bb_instructions) s'` >>
  gvs[] >> rename1 `ev_step _ _ _ _ _ _ s' = OK u` >>
  Cases_on `is_terminator (EL s'.vs_inst_idx bb.bb_instructions).inst_opcode`
  >- (Cases_on `u.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
      `s'.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
        (gvs[bb_well_formed_def] >> first_x_assum irule >> simp[]) >>
      `inst_wf (EL s'.vs_inst_idx bb.bb_instructions)` by gvs[EVERY_EL] >>
      `(EL s'.vs_inst_idx bb.bb_instructions).inst_opcode <> GAS /\
       (EL s'.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE` by
        (Cases_on `(EL s'.vs_inst_idx bb.bb_instructions).inst_opcode` >>
         gvs[is_terminator_def]) >>
      `step_inst_base (EL s'.vs_inst_idx bb.bb_instructions) s' = OK t` by
        gvs[Once ev_step_def] >>
      drule_all step_inst_base_term_succs >> strip_tac >>
      simp[bb_succs_def] >>
      Cases_on `bb.bb_instructions` >> gvs[bb_well_formed_def, LAST_EL, MEM_nub, MEM_REVERSE]) >>
  simp[] >> strip_tac >>
  first_x_assum (qspec_then
    `LENGTH bb.bb_instructions - SUC s'.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >> goal_assum (drule_at Any) >> simp[]
QED
