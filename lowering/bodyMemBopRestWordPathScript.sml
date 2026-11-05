(* Allocation boundaries for the memory membership suffix. *)
Theory bodyMemBopRestWordPath
Ancestors
  fragGasMode allocaHistory venomMemProofs venomMemProps exprLoweringProps

Theorem rest_word_step_frontier:
  step_inst fuel ctx inst s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[Once venomExecSemanticsTheory.step_inst_def, AllCaseEqs()] >>
      mp_tac (Q.ISPEC `\s:venom_state. s.vs_alloca_next`
        venomInstProofs1Theory.bind_outputs_preserves) >>
      simp[venomStateTheory.update_var_def] >>
      disch_then drule >>
      Cases_on `ret.iret_adopt_fmp` >> simp[venomExecSemanticsTheory.merge_callee_state_def,
        venomExecSemanticsTheory.adopt_return_fmp_def, AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (drule venomMemPropsTheory.step_inst_alloca_alloca_next_mono >>
      simp[venomInstTheory.is_alloca_op_def]) >>
  `step_inst_base inst s = OK t` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  metis_tac[venomMemProofsTheory.step_inst_base_preserves_alloca_next,
    arithmeticTheory.LESS_EQ_REFL]
QED

Theorem rest_word_state_alloca_inv:
  stmt_state_rel ctx func cenv cx es s ==> alloca_inv s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def]
QED
