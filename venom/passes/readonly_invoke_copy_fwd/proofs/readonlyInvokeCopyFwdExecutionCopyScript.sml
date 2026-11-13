Theory readonlyInvokeCopyFwdExecutionCopy
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdCopyFrontier
  readonlyInvokeCopyFwdMemory readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdOperationalGuards readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdCalls readonlyInvokeCopyFwdGlobalSupport
  internalReturnCopyFwdSim o1LowerDloadOccurrence o1LowerDloadShared
  ptrDiscipline taintAgree venomExecSemantics venomState venomInst
  finite_map list pred_set words arithmetic

Theorem ricf_execution_zero_copy_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = MCOPY /\
  inst.inst_operands = [dop;rop;Lit 0w] /\ inst.inst_outputs = [] /\
  step_inst fuel C inst s = OK u /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  step_inst fuel Ct nop t = OK t /\
  ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst u) HP
    (occurrence_step a HP H inst u) ledger E sites maps targets
    (step_taint inst s u rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `?d r. eval_operand dop s = SOME d /\ eval_operand rop s = SOME r /\
    u = mcopy (w2n d) (w2n r) 0 s` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, eval_operand_def,
      AllCaseEqs()] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `step_prov PG G inst u = G /\ step_taint inst s u tn = tn /\
    step_taint inst s u rt = rt /\ occurrence_sites_step a B inst u = B /\
    occurrence_step a HP H inst u = H` by
    (simp[step_prov_def, occurrence_sites_step_def, occurrence_step_def,
       set_prov_def, DRESTRICT_UNIV] >>
     `!T. step_taint inst s u T = T` suffices_by simp[] >>
     gen_tac >> drule_all step_taint_mcopy >> simp[EXTENSION]) >>
  `ricf_heterogeneous_source_ledger vs C stk PG G tn fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H ledger` by
    (drule_all ricf_heterogeneous_source_ledger_actual_next >> simp[]) >>
  `ricf_map_origins vs C ctx0 log stk PG G tn fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) U B sites` by
    (drule_all ricf_map_origins_next >> simp[]) >>
  `ricf_frame_agree D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G rt u t` by
    (simp[] >> irule ricf_frame_source_mcopy_frontier >>
     simp[SUBSET_DEF, EXTENSION] >> metis_tac[LESS_EQ_CASES]) >>
  `ricf_live_stack_agree D (ricf_original_copy_ids C) rt maps stk targets u t` by
    (simp[] >> irule ricf_live_stack_source_mcopy_frontier >>
     simp[EXTENSION] >> metis_tac[LESS_EQ_CASES]) >>
  `ircf_cross rt (ricf_phase_ranges 0 ledger) u t` by
    (simp[] >> irule ricf_cross_source_mcopy_frame >>
     simp[EXTENSION] >> metis_tac[LESS_EQ_CASES]) >>
  `ricf_cert_crosses rt (ricf_phase_stack_ranges stk ledger) stk u t` by
    (fs[ricf_cert_crosses_def, EVERY_MEM] >>
     simp[ricf_cert_crosses_def, EVERY_MEM] >> rpt strip_tac >>
     simp[] >>
     irule ricf_cross_source_mcopy_frame >>
     simp[EXTENSION] >> metis_tac[LESS_EQ_CASES]) >>
  `ricf_support_agree B E rt u t` by metis_tac[ricf_support_zero_copy] >>
  simp[step_inst_def, step_inst_base_opcode_eqs] >>
  gvs[ircf_dead_def, mcopy_def, write_memory_with_expansion_def] >>
  conj_tac
  >- (qpat_assum `ricf_frame_agree _ _ _ _ _ _ (_ with vs_memory := _) _`
        (mp_then Any (qspec_then `SUC s.vs_inst_idx` mp_tac) ricf_frame_inst_idx) >>
      simp[ircf_dead_def]) >>
  conj_tac
  >- fs[ricf_live_stack_agree_def, merge_callee_state_def] >>
  conj_tac >-
    (qpat_x_assum `ircf_cross _ _ (_ with vs_memory := _) _` mp_tac >>
     simp[ircf_cross_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_cert_crosses _ _ _ (_ with vs_memory := _) _` mp_tac >>
     simp[ricf_cert_crosses_def, ircf_cross_def, merge_callee_state_def]) >>
  qpat_x_assum `ricf_support_agree _ _ _ (_ with vs_memory := _) _` mp_tac >>
  simp[ricf_support_agree_def]
QED
