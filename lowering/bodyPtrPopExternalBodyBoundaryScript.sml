Theory bodyPtrPopExternalBodyBoundary
Ancestors bodyPtrPopStatementBoundary bodyPtrPopLockBoundary
  bodyPtrPopReturnProducerBoundary bodyPtrPopArgumentsBoundary
  bodyPtrPopEntryChecksBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopMaterialization moduleLowering compileEnv

Theorem pop_guarded_body_boundary:
  supported_stmts tops bindings stmts /\ pop_comp_boundary sa /\
  compile_guarded_body ce nr key trans view stmts ret sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `nr` >> Cases_on `ret` >>
  simp[compile_guarded_body_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_all (cj 2 pop_compile_statements_boundary) >> simp[],
     drule_all pop_compile_nonreentrant_lock_boundary >> simp[],
     drule_all pop_compile_nonreentrant_unlock_boundary >> simp[],
     (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >> IF_CASES_TAC >>
      simp[comp_return_def, comp_ignore_bind_def] >> strip_tac >>
      rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
           disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
      FIRST_PROVE
        [drule_all pop_compile_nonreentrant_unlock_boundary >> simp[],
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
         gvs[comp_return_def] >> NO_TAC]),
     gvs[comp_return_def, comp_get_def] >> NO_TAC]
QED

Theorem pop_external_function_body_boundary:
  supported_stmts tops bindings stmts /\ pop_comp_boundary sa /\
  compile_external_function_body ce args nr key trans view stmts ret sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_external_function_body_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST_PROVE [drule_all pop_register_positional_args_boundary >> simp[],
    drule_all pop_guarded_body_boundary >> simp[]]
QED

Theorem pop_fallback_body_boundary:
  supported_stmts tops bindings stmts /\ pop_comp_boundary sa /\
  compile_fallback_body ce payable nr key trans view stmts ret sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `payable` >> simp[compile_fallback_body_def, comp_ignore_bind_def] >>
  rpt strip_tac >> dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST_PROVE [drule_all pop_payable_check_boundary >> simp[],
    drule_all pop_guarded_body_boundary >> simp[], gvs[comp_return_def]]
QED
