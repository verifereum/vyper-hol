(* Memory-free arithmetic safety does not require scalar provenance. *)
Theory bodyPtrWordBuiltinsArithmeticSteps
Ancestors ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  venomExecProofs list contextCodegenRel codegenRel

Theorem word_arithmetic_ptr_safe_step:
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  MEM inst.inst_opcode
    [SUB; MUL; Div; Exp; ADDMOD; MULMOD; SGT; SLT; ISZERO; OR; AND; ASSERT] ==>
  ptr_safe_step D lo fuel ctx fn PG G tn inst s
Proof
  simp[MEM] >> strip_tac >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_literal_comparison_ptr_safe_step:
  (!arg. MEM arg inst.inst_operands ==> op_taint tn arg = {}) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  MEM inst.inst_opcode [LT; GT; EQ] /\
  (inst.inst_operands = [op; Lit w] \/ inst.inst_operands = [Lit w; op]) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn inst s
Proof
  simp[MEM] >> strip_tac >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_arithmetic_out_taint:
  MEM inst.inst_opcode
    [SUB; MUL; Div; Exp; ADDMOD; MULMOD; SGT; SLT; ISZERO; OR; AND; ASSERT; LT; GT; EQ] ==>
  out_taint tn inst s = {}
Proof
  simp[MEM] >> strip_tac >>
  (namedCases_on `inst.inst_operands` ["", "a rest"]
  >- simp[out_taint_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def]) >>
  Cases_on `tail` >> simp[out_taint_def])
QED

Theorem word_arithmetic_output_clean:
  MEM inst.inst_opcode
    [SUB; MUL; Div; Exp; ADDMOD; MULMOD; SGT; SLT; ISZERO; OR; AND; ASSERT; LT; GT; EQ] /\
  inst.inst_outputs = [out] ==>
  op_taint (step_taint inst s t tn) (Var out) = {}
Proof
  strip_tac >> drule word_arithmetic_out_taint >> strip_tac >>
  simp[op_taint_def, step_taint_def, set_var_taint_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
