Theory bodyPtrBytestringBuiltinsCalldataCopy
Ancestors
  fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState finite_map codegenRel memLocDefs contextCodegenRel

Theorem ptr_inst_ok_calldatacopy_operand:
  !D ctx fn G tn s id dst src count n fuel.
    eval_operand count s = SOME n /\ op_taint tn count = {} /\
    op_taint tn src = {} /\ ptr_covers G tn dst s (w2n n) /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id CALLDATACOPY [Var dst; src; count] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, sized_source_write_range_def,
       eval_operand_def, mem_write_ops_def] >>
  rpt conj_tac
  >- (Cases_on `eval_operand src s` >> simp[] >> rpt strip_tac >> gvs[])
  >- (metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, combinTheory.K_THM,
                   opcode_case_def] >>
  Cases_on `eval_operand src s` >>
  simp[eval_operand_def, write_memory_with_expansion_def]
QED
