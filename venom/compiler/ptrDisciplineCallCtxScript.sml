(*
 * The call context along frame_reachable: entering a block and a
 * terminator's step keep vs_call_ctx, so every saved frame has the active
 * frame's call context.
 *
 * TOP-LEVEL:
 *   ptr_enters_block_call_ctx  - entering a block keeps the call context
 *   ptr_terminator_call_ctx    - a terminator's OK step keeps it
 *   ptr_reachable_stack_call_ctx - every saved frame has the active one
 *)
Theory ptrDisciplineCallCtx
Ancestors
  ptrDiscipline contextCodegenRel venomExecProofs venomInstProofs
  venomInstProofs1 venomExecSemantics venomState venomInst list

Theorem ptr_enters_block_call_ctx:
  enters_block fn s t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem ptr_terminator_call_ctx:
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[Once step_inst_def, step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), jump_to_def] >> pairarg_tac >> gvs[]
QED

Theorem ptr_reachable_stack_call_ctx:
  !vs C stk PG G tn fn inst s. frame_reachable vs C stk PG G tn fn inst s ==>
  !f. MEM f stk ==> s.vs_call_ctx = f.cf_state.vs_call_ctx
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> drule_all venomInstProofsTheory.step_preserves_call_ctx >>
      strip_tac >> simp[])
  >- (rpt strip_tac >> drule_all ptr_terminator_call_ctx >>
      drule ptr_enters_block_call_ctx >> metis_tac[])
  >- (rpt strip_tac >> drule ptr_enters_block_call_ctx >>
      qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
      simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac >>
  `s'.vs_call_ctx = f.cf_state.vs_call_ctx` by
    (qspec_then `(\u. u.vs_call_ctx)` mp_tac bind_outputs_preserves >>
     simp[update_var_def] >> disch_then drule >>
     Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  gvs[] >> metis_tac[]
QED
