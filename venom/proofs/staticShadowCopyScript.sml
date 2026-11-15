Theory staticShadowCopy
Ancestors
  staticShadowFrame staticShadowPrim staticShadowDefs venomExecSemantics
  venomState venomInst list
Libs
  stepInstBaseLib

Theorem static_shadow_copy3[local]:
  MEM inst.inst_opcode [CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  `sh.vs_call_ctx.cc_calldata = s.vs_call_ctx.cc_calldata /\
   sh.vs_returndata = s.vs_returndata /\
   sh.vs_data_section = s.vs_data_section /\ sh.vs_code = s.vs_code` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  fs[] >> with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `rest` ["", "b more"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `more` ["", "c tail"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand a s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand b s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand c s` >> simp[] >>
  rpt IF_CASES_TAC >> simp[static_shadow_result_rel_def,
    static_shadow_memory_writes] >>
  simp[write_memory_with_expansion_def]
QED

Theorem static_shadow_extcodecopy[local]:
  inst.inst_opcode = EXTCODECOPY /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  `sh.vs_accounts = s.vs_accounts` by metis_tac[static_shadow_rel_fields] >>
  with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `rest` ["", "b more"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `more` ["", "c last"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `last` ["", "d tail"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand a s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand b s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand c s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand d s` >> simp[static_shadow_result_rel_def,
    static_shadow_memory_writes] >> simp[write_memory_with_expansion_def]
QED

Theorem static_shadow_sha3[local]:
  inst.inst_opcode = SHA3 /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  `sh.vs_memory = s.vs_memory` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `rest` ["", "b tail"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand a s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand b s` >> simp[static_shadow_result_rel_def] >>
  namedCases_on `inst.inst_outputs` ["", "out tail"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def,
    static_shadow_rel_update_var] >> simp[update_var_def]
QED

Theorem static_shadow_copy:
  MEM inst.inst_opcode [CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY;
                        EXTCODECOPY; SHA3] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >> fs[] >>
  FIRST [irule static_shadow_copy3 >> simp[] >> NO_TAC,
         irule static_shadow_extcodecopy >> simp[] >> NO_TAC,
         irule static_shadow_sha3 >> simp[] >> NO_TAC]
QED
