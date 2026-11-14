Theory staticShadowBase
Ancestors
  staticShadowCall staticShadowControl staticShadowCopy staticShadowForbidden staticShadowDynamic
  staticShadowFrame staticShadowPrim staticShadowDefs venomExecSemantics venomCallOracleDefs
  extCallOracle venomState venomInst list finite_map
Libs
  stepInstBaseLib

Theorem static_shadow_mcopy[local]:
  inst.inst_opcode = MCOPY /\ s.vs_call_ctx.cc_static /\
  static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `rest` ["", "b more"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `more` ["", "c tail"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand a s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand b s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand c s` >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_memory_writes, mcopy_def, write_memory_with_expansion_def]
QED

Theorem static_shadow_write2_undefined[local]:
  eval_operands inst.inst_operands s = NONE ==>
  static_shadow_result_rel (exec_write2 f inst s) r
Proof
  strip_tac >> Cases_on `exec_write2 f inst s` >>
  gvs[static_shadow_result_rel_def, exec_write2_def, AllCaseEqs(),
      eval_operands_def]
QED

Theorem static_shadow_storage[local]:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\ s.vs_call_ctx.cc_static ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >> fs[] >> with_opcode_clause simp >>
  Cases_on `eval_operands inst.inst_operands s` >>
  simp[static_shadow_write2_undefined] >>
  simp[static_shadow_result_rel_def]
QED

Theorem static_shadow_istore[local]:
  inst.inst_opcode = ISTORE /\ s.vs_call_ctx.cc_static /\
  static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `rest` ["", "b tail"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand a s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand b s` >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_istore]
QED

Theorem static_shadow_jumps[local]:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  fs[] >> with_opcode_clause simp >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_controls, jump_to_def]
QED

Theorem static_shadow_frame_ops[local]:
  MEM inst.inst_opcode [GETFMP; SETFMP; DALLOCA; INITIAL_FMP; BUMP;
    FMP_PARAM; RETPC_PARAM; PARAM; ASSIGN; NOP] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  `sh.vs_fmp = s.vs_fmp /\ sh.vs_initial_fmp = s.vs_initial_fmp /\
   sh.vs_params = s.vs_params /\ sh.vs_return_pc_token = s.vs_return_pc_token` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  fs[] >> with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[static_shadow_result_rel_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[static_shadow_result_rel_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def,
    static_shadow_rel_update_var, static_shadow_rel_updates] >>
  simp[update_var_def]
QED

Theorem static_shadow_gas[local]:
  inst.inst_opcode = GAS /\ s.vs_call_ctx.cc_static /\
  static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `sh.vs_gas_readings = s.vs_gas_readings` by
    metis_tac[static_shadow_rel_fields] >>
  with_opcode_clause simp >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_gas_def, static_shadow_result_rel_def] >>
  Cases_on `outs` >> simp[exec_gas_def, static_shadow_result_rel_def] >>
  Cases_on `s.vs_gas_readings` >>
  simp[static_shadow_result_rel_def, static_shadow_rel_update_var,
       static_shadow_rel_updates] >>
  simp[update_var_def]
QED

Theorem static_shadow_alloca[local]:
  inst.inst_opcode = ALLOCA /\ s.vs_call_ctx.cc_static /\
  static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `sh.vs_allocas = s.vs_allocas /\ sh.vs_alloca_next = s.vs_alloca_next` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >>
  simp[static_shadow_result_rel_def] >>
  Cases_on `a` >> simp[static_shadow_result_rel_def] >>
  Cases_on `rest` >> simp[static_shadow_result_rel_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_alloca_def, static_shadow_result_rel_def] >>
  Cases_on `outs` >> simp[exec_alloca_def, static_shadow_result_rel_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[static_shadow_result_rel_def, static_shadow_rel_update_var,
       static_shadow_rel_updates] >>
  simp[update_var_def]
QED

Theorem static_shadow_base_noncall:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  `!ops. eval_operands ops sh = eval_operands ops s` by
    metis_tac[static_shadow_rel_eval_operands] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  FIRST [irule static_shadow_gas >> simp[] >> NO_TAC,
         irule static_shadow_alloca >> simp[] >> NO_TAC,
         irule static_shadow_frame_ops >> simp[] >> NO_TAC,
         irule static_shadow_control >> simp[] >> NO_TAC,
         irule static_shadow_copy >> simp[] >> NO_TAC,
         irule static_shadow_forbidden >> simp[] >> NO_TAC,
         irule static_shadow_dret >> simp[] >> NO_TAC,
         irule static_shadow_mcopy >> simp[] >> NO_TAC,
         irule static_shadow_istore >> simp[] >> NO_TAC,
         irule static_shadow_jumps >> simp[] >> NO_TAC,
         irule static_shadow_storage >> simp[] >> NO_TAC,
         ALL_TAC] >>
  with_opcode_clause simp >>
  FIRST [irule static_shadow_pure1 >> simp[],
         irule static_shadow_pure2 >> simp[],
         irule static_shadow_pure3 >> simp[],
         irule static_shadow_read0 >> simp[] >>
           gvs[static_shadow_rel_def, static_shadow_def,
               venom_state_component_equality],
         irule static_shadow_read1 >> simp[] >>
           gvs[static_shadow_rel_def, static_shadow_def,
               venom_state_component_equality, contract_storage_def,
               contract_transient_def, sload_def, tload_def,
               mload_def, read_memory_def],
         irule static_shadow_write2 >> simp[] >> rpt gen_tac >>
           simp[static_shadow_memory_writes, mstore_def, mstore8_def],
         ALL_TAC] >>
  simp[static_shadow_result_rel_def]
QED

Theorem static_shadow_base:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL]`
  >- (irule static_shadow_calls >> simp[]) >>
  irule static_shadow_base_noncall >> simp[]
QED
