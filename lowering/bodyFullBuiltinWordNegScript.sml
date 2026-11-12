(* Joint Neg simulation: its checked arithmetic suffix. *)
Theory bodyFullBuiltinWordNeg
Ancestors
  bodyFullGhostFrame bodyFullShared bodyFullPreds bodySimFull
  gasOutcomeFullCompose gasOutcomeFullStmts fragGasSeqPtr fragGasEmitCtrl
  exprSimWordBuiltins exprSimUnopProps exprSimSource
  ptrSafeRun ptrDiscipline exprLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv venomExecSemantics venomInst venomState
  list rich_list finite_map codegenRel contextCodegenRel

Theorem word_neg_emission:
  !x ty sa op sb.
    compile_neg x ty sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) ASSERT
         [Var (STRING #"%" (toString sa.cs_next_var))] [];
       mk_inst (sa.cs_next_id+2) SUB [Lit 0w; x]
         [STRING #"%" (toString (sa.cs_next_var+1))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+1)))
Proof
  rpt gen_tac >> Cases_on `type_bounds ty` >>
  simp[compile_neg_def, LET_THM, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
    fresh_var_def, emit_def, emitted_insts_def, DROP_LENGTH_APPEND,
    arithmeticTheory.ADD_ASSOC] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem word_neg_arithmetic_ptr:
  compile_neg x ty sa = (op,sb) /\
  MEM i [mk_inst sa.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
           [STRING #"%" (toString sa.cs_next_var)];
         mk_inst (sa.cs_next_id+2) SUB [Lit 0w; x]
           [STRING #"%" (toString (sa.cs_next_var+1))]] /\
  op_taint tn x = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn i s
Proof
  strip_tac >> gvs[] >>
  (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  conj_tac >- (gen_tac >> Cases_on `op' = x` >>
    gvs[] >> Cases_on `op'` >> simp[op_taint_def]) >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[])
QED

Theorem word_neg_assert_ptr:
  compile_neg x ty sa = (op,sb) /\
  op_taint tn (Var (STRING #"%" (toString sa.cs_next_var))) = {} /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst (sa.cs_next_id+1) ASSERT
      [Var (STRING #"%" (toString sa.cs_next_var))] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  Cases_on `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) s` >>
  simp[] >> Cases_on `x' = 0w` >> simp[]
QED
