Theory bodyPtrPopStatementFlowBoundary
Ancestors bodyPtrPopStatementControl bodyPtrPopCompilerBoundary
  bodyPtrPopMutualBoundary bodyPtrPopCompileDomain bodyPtrPopMaterialization
  stmtLowering compileEnv exprLowering emitHelper supportedStmts venomInst

Theorem pop_stmt_break_boundary:
  pop_comp_boundary sa /\ compile_stmt ce lc ty Break sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `lc` >> simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
               gvs[comp_return_def]]
QED

Theorem pop_stmt_continue_boundary:
  pop_comp_boundary sa /\ compile_stmt ce lc ty Continue sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `lc` >> simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
               gvs[comp_return_def]]
QED

Theorem pop_stmt_if_boundary:
  (!s r t. pop_comp_boundary s /\ compile_stmts ce lc ty yes s = (r,t) ==>
    pop_comp_boundary t) /\
  (!s r t. pop_comp_boundary s /\ compile_stmts ce lc ty no s = (r,t) ==>
    pop_comp_boundary t) /\ supported_pure_expr tops cond /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (If cond yes no) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [first_x_assum drule_all >> simp[],
     drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_all pop_fresh_label_boundary >> simp[],
     drule_all pop_comp_boundary_new_block >> simp[],
     drule_all pop_emit_jmp_if_not_terminated_boundary >> simp[],
     (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
      disch_then irule >> simp[] >> rpt strip_tac >> drule pop_domain_pure >> strip_tac >>
      drule_all (cj 1 pop_compile_mutual_boundary) >> simp[]),
     (qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >>
      IF_CASES_TAC >> simp[] >> strip_tac >>
      rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
           disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
      FIRST_PROVE [drule_all pop_comp_boundary_new_block >> simp[], gvs[comp_return_def]]),
     gvs[comp_return_def, comp_get_def]]
QED
