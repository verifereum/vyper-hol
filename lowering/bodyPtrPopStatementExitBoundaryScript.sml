Theory bodyPtrPopStatementExitBoundary
Ancestors bodyPtrPopReturnProducerBoundary bodyPtrPopStatementGuards
  bodyPtrPopMutualBoundary bodyPtrPopCompileDomain bodyPtrPopCompilerBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopMaterialization bodyPtrPopAllocationBoundary
  bodyPtrPopTypedCopyBoundary stmtLowering context compileEnv exprLowering emitHelper
  supportedStmts venomInst

Theorem pop_stmt_append_boundary:
  supported_pure_expr tops e /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (Append bt e) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[compile_stmt_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >>
  (conj_tac >- (rpt strip_tac >>
    drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
    disch_then irule >> simp[] >> rpt strip_tac >>
    drule pop_domain_pure >> strip_tac >>
    drule_all (cj 1 pop_compile_mutual_boundary) >> simp[])) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >>
  (conj_tac >- (rpt strip_tac >>
    qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >> IF_CASES_TAC >>
    simp[comp_ignore_bind_def] >> strip_tac >>
    rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
         disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
    FIRST_PROVE [drule_all pop_compile_alloc_buffer_boundary >> simp[],
      drule_all pop_compile_store_memory_boundary >> simp[], gvs[comp_return_def]])) >>
  rpt strip_tac >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[Once comp_bind_def, comp_return_def] >> strip_tac >>
  drule_at (Pat `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    pop_compile_dynarray_append_boundary >> disch_then irule >> simp[] >>
  Cases_on `infer_array_location ce (target_to_expr bt)` >>
  simp[load_opc_for_def, store_opc_for_def]
QED

Theorem pop_stmt_return_none_boundary:
  pop_comp_boundary sa /\ compile_stmt ce lc ty (Return NONE) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `ce.ce_return_pc` >>
  TRY (rename1 `ce.ce_return_pc = SOME rpc_loc` >> Cases_on `rpc_loc`) >>
  Cases_on `ce.ce_ctor_exit_label` >>
  Cases_on `ce.ce_nonreentrant` >> PairCases_on `r'` >>
  simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     (qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >>
      IF_CASES_TAC >> simp[comp_return_def] >> strip_tac >> gvs[] >>
      drule_all pop_compile_nonreentrant_unlock_boundary >> simp[]),
     gvs[comp_return_def]]
QED

Theorem pop_stmt_return_some_boundary:
  supported_expr tops e /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (Return (SOME e)) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `ce.ce_return_pc` >>
  TRY (rename1 `ce.ce_return_pc = SOME rpc_loc` >> Cases_on `rpc_loc`) >>
  simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_all pop_compile_internal_return_from_env_boundary >> simp[],
     drule_all pop_compile_external_return_boundary >> simp[],
     (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
      disch_then irule >> simp[] >> rpt strip_tac >>
      drule_all pop_compile_supported_boundary >> simp[]),
     (qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >>
      IF_CASES_TAC >> simp[] >> strip_tac >>
      rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
           disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
      FIRST_PROVE [drule_all pop_compile_alloc_buffer_boundary >> simp[],
        drule_all pop_compile_store_memory_typed_boundary >> simp[], gvs[comp_return_def]]),
     gvs[comp_return_def]]
QED
