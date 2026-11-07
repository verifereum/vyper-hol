Theory bodyPtrPopRuntimeBoundary
Ancestors bodySim bodyPtrPopStatementBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopMaterialization bodyPtrPopAllocationBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopReturnProducerBoundary bodyPtrPopInternalParamsBoundary
  bodyPtrPopLockBoundary moduleLowering compileEnv

Theorem pop_body_inv_runtime:
  body_inv tops ctx ce cx /\ ~ce.ce_is_ctor ==>
  ~cx.in_deploy /\ ?policy unit.
    lower_vyper_runtime_unit tops policy = SOME unit /\ ctx = unit.cu_context
Proof
  simp[body_inv_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED


Theorem pop_internal_function_boundary:
  supported_stmts tops bindings stmts /\ pop_comp_boundary sa /\
  compile_internal_function ce params has_buf nr key trans view ctor imm stmts ret
    sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `ret` >> Cases_on `ce.ce_returns_count > 0` >> Cases_on `nr` >>
  simp[compile_internal_function_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_all (cj 2 pop_compile_statements_boundary) >> simp[],
     drule_all pop_internal_param_decls_boundary >> simp[],
     drule_all pop_materialize_internal_params_boundary >> simp[],
     drule_all pop_compile_alloc_buffer_boundary >> simp[],
     drule_all pop_compile_fixed_region_with_id_boundary >> simp[],
     drule_all pop_compile_nonreentrant_lock_boundary >> simp[],
     drule_all pop_compile_nonreentrant_unlock_boundary >> simp[],
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >> IF_CASES_TAC >>
      simp[comp_return_def, comp_ignore_bind_def] >> strip_tac >>
      rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
           disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
      FIRST_PROVE
        [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
         drule_all pop_compile_fixed_region_with_id_boundary >> simp[],
         drule_all pop_compile_nonreentrant_lock_boundary >> simp[],
         drule_all pop_compile_nonreentrant_unlock_boundary >> simp[],
         gvs[comp_return_def] >> NO_TAC]),
     gvs[comp_return_def, comp_get_def] >> NO_TAC]
QED
