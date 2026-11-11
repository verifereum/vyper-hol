(* Source-independent checked bounds for clean provenance-free words. *)
Theory bodyPtrCodeSliceBounds
Ancestors
  exprSimSliceBounds typedCopyPtr exprSendPtr bodyPtrHashBuiltinsGhostFrame
  fragGasSeqPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState codegenRel contextCodegenRel compileEnv
  loweringStateRelDefs words finite_map pred_set list

Theorem slice_bounds_compare_checked:
  !D ctx fn G tn s id opc a b dst fuel.
    (opc = LT \/ opc = GT \/ opc = OR) /\
    op_taint tn a = {} /\ op_taint tn b = {} /\
    op_prov G a = NONE /\ op_prov G b = NONE /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [a;b] [dst]) s
Proof
  rpt gen_tac >> strip_tac >>
  `!u. a = Var u ==> u NOTIN FDOM G` by
    (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  `!u. b = Var u ==> u NOTIN FDOM G` by
    (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem slice_bounds_iszero_checked:
  !D ctx fn G tn s id a dst fuel.
    op_taint tn a = {} /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ISZERO [a] [dst]) s
Proof
  rpt gen_tac >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
