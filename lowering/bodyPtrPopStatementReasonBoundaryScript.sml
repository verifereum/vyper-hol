Theory bodyPtrPopStatementReasonBoundary
Ancestors bodyPtrPopReasonLogBoundary bodyPtrPopMutualBoundary bodyPtrPopCompileDomain
  bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary bodyPtrPopMaterialization
  bodyPtrPopAllocationBoundary stmtLowering compileEnv exprLowering emitHelper
  supportedStmts supportedExprs venomInst bodyPtrPopAbiEncodeBoundary

Theorem pop_stmt_raise_boundary:
  supported_raise_reason tops reason /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (Raise reason) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `reason` >> simp[supported_raise_reason_def, compile_stmt_def] >>
  rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_all pop_compile_reason_message_boundary >> simp[],
     drule_all pop_compile_revert_with_reason_boundary >> simp[]]
QED

Theorem pop_stmt_assert_boundary:
  supported_pure_expr tops cond /\ supported_assert_reason tops reason /\
  pop_comp_boundary sa /\
  compile_stmt ce lc ty (Assert cond reason) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `reason` >> simp[supported_assert_reason_def, compile_stmt_def,
                           comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_all pop_compile_reason_message_boundary >> simp[],
     drule_all pop_compile_revert_with_reason_boundary >> simp[],
     drule_all pop_fresh_label_boundary >> simp[],
     drule_all pop_comp_boundary_new_block >> simp[],
     (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
      disch_then irule >> simp[] >> rpt strip_tac >>
      drule pop_domain_pure >> strip_tac >>
      drule_all (cj 1 pop_compile_mutual_boundary) >> simp[]),
     gvs[comp_return_def]]
QED

Theorem pop_stmt_log_boundary:
  supported_log tops id es /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (Log id es) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[supported_log_def, supported_pure_exprs_every, compile_stmt_def,
       comp_ignore_bind_def] >>
  Cases_on `ce.ce_event_info (nsid_to_string id)` >>
  TRY (rename1 `SOME info` >> PairCases_on `info`) >>
  rpt strip_tac >> gvs[] >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_all pop_compile_log_eval_all_boundary >> simp[],
     drule_all pop_compile_log_topic_ops_boundary >> simp[],
     (qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >>
      IF_CASES_TAC >> simp[] >> strip_tac >>
      rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
           disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
      FIRST_PROVE
        [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
         drule_all pop_compile_alloc_buffer_boundary >> simp[],
         drule_all pop_compile_log_store_data_boundary >> simp[],
         drule_all pop_compile_abi_encode_to_buf_boundary >> simp[],
         gvs[comp_return_def]]), gvs[comp_return_def]]
QED
