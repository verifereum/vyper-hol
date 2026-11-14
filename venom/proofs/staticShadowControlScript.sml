Theory staticShadowControl
Ancestors
  staticShadowFrame staticShadowPrim staticShadowDefs venomExecSemantics
  venomState venomInst list
Libs
  stepInstBaseLib

Theorem static_shadow_ret[local]:
  MEM inst.inst_opcode [RET; RETFMP] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!ops. eval_operands ops sh = eval_operands ops s` by
    metis_tac[static_shadow_rel_eval_operands] >>
  `sh.vs_fmp = s.vs_fmp` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  fs[] >> with_opcode_clause simp >>
  Cases_on `eval_operands inst.inst_operands s` >>
  simp[static_shadow_result_rel_def] >>
  Cases_on `x` >> simp[static_shadow_result_rel_def]
QED

Theorem static_shadow_termination[local]:
  MEM inst.inst_opcode [STOP; SINK] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >> fs[] >> with_opcode_clause simp >>
  rewrite_tac[GSYM set_returndata_def] >>
  simp[static_shadow_result_rel_def, static_shadow_rel_controls] >>
  simp[halt_state_def, set_returndata_def]
QED

Theorem static_shadow_return_revert[local]:
  MEM inst.inst_opcode [RETURN; REVERT] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  `sh.vs_memory = s.vs_memory` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  fs[] >> with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `rest` ["", "b tail"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand a s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand b s` >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_controls, halt_state_def, set_returndata_def]
QED

Theorem static_shadow_assert[local]:
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  fs[] >> with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a tail"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand a s` >> simp[static_shadow_result_rel_def] >>
  IF_CASES_TAC >> simp[static_shadow_result_rel_def]
QED

Theorem static_shadow_control:
  MEM inst.inst_opcode [RET; RETFMP; STOP; RETURN; REVERT; SINK;
                        ASSERT; ASSERT_UNREACHABLE] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  fs[] >>
  FIRST [irule static_shadow_ret >> simp[] >> NO_TAC,
         irule static_shadow_termination >> simp[] >> NO_TAC,
         irule static_shadow_return_revert >> simp[] >> NO_TAC,
         irule static_shadow_assert >> simp[] >> NO_TAC]
QED
