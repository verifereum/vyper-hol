Theory bodyPtrPopStatementLoopBoundary
Ancestors bodyPtrPopStatementControl bodyPtrPopStatementGuards
  bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary bodyPtrPopMaterialization
  bodyPtrPopAllocationBoundary bodyPtrPopMutualBoundary bodyPtrPopCompileDomain
  bodyPtrPopFiniteProducerBoundary bodyPtrPopBaseExprBoundary
  stmtLowering compileEnv exprLowering emitHelper supportedStmts venomInst

Theorem pop_loop_endpoint_boundary[local]:
  (supported_pure_expr tops e \/ (?ty n. e = Literal ty (IntL n))) /\
  pop_comp_boundary sa /\ lower_value compile_expr ce fty e sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
  disch_then irule >> simp[] >> rpt strip_tac >> FIRST_PROVE
    [(drule pop_domain_pure >> strip_tac >>
      drule_all (cj 1 pop_compile_mutual_boundary) >> simp[]),
     (gvs[] >> qpat_x_assum `compile_expr _ _ (Literal _ _) _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      drule_all pop_compile_literal_vv_boundary >> simp[])]
QED

Theorem pop_range_endpoints:
  supported_iterator tops fty (Range a b) bound ==>
  (supported_pure_expr tops a \/ (?ty n. a = Literal ty (IntL n))) /\
  (supported_pure_expr tops b \/ (?ty n. b = Literal ty (IntL n)))
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[supported_iterator_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> metis_tac[]
QED

Theorem pop_range_rounds_boundary[local]:
  pop_comp_boundary sa /\
  (case (a,b) of
    (Literal _ (IntL start_n), Literal _ (IntL end_n)) =>
      return (Lit (i2w end_n - i2w start_n))
  | _ => emit_op SUB [last; first]) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `a` >> Cases_on `b` >> simp[] >> rpt strip_tac >>
  FIRST_PROVE
    [(drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[] >> NO_TAC),
     (Cases_on `l` >> Cases_on `l'` >> gvs[comp_return_def] >>
      drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[])]
QED

Theorem pop_range_check_boundary[local]:
  pop_comp_boundary sa /\
  (case (a,b) of
    (Literal _ (IntL _), Literal _ (IntL _)) => return ()
  | _ => compile_range_bound_checks first last rounds bound signed) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `a` >> Cases_on `b` >> simp[] >> rpt strip_tac >>
  FIRST_PROVE
    [(drule_all pop_compile_range_bound_checks_boundary >> simp[] >> NO_TAC),
     (Cases_on `l` >> Cases_on `l'` >> gvs[comp_return_def] >>
      drule_all pop_compile_range_bound_checks_boundary >> simp[])]
QED

Theorem pop_range_variable_store_boundary[local]:
  pop_comp_boundary sa /\
  (case dest of
    SOME (MemLoc off _) => emit_void MSTORE [Lit (n2w off); v]
  | SOME (PtrVar dst_op _) => emit_void MSTORE [dst_op; v]
  | _ => emit_void INVALID []) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `dest`
  >- (simp[] >> rpt strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
  Cases_on `x` >> simp[] >> rpt strip_tac >>
  drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]
QED

Theorem pop_stmt_for_range_boundary:
  (!ce' exit incr s r t. pop_comp_boundary s /\
    compile_stmts ce' (InLoop exit incr) ty loop_body s = (r,t) ==> pop_comp_boundary t) /\
  supported_iterator tops fty (Range a b) bound /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (For id fty (Range a b) bound loop_body) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  drule pop_range_endpoints >> disch_then assume_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [(drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_loop_endpoint_boundary >>
      disch_then irule >> simp[] >> qexists_tac `tops` >> metis_tac[]),
     drule_all pop_declare_local_boundary >> simp[],
     drule_all pop_emit_local_alloca_boundary >> simp[],
     drule_all pop_fresh_label_boundary >> simp[],
     drule_all pop_fresh_var_boundary >> simp[],
     drule_all pop_comp_boundary_new_block >> simp[],
     drule_all pop_emit_jmp_if_not_terminated_boundary >> simp[],
     drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     first_x_assum drule_all >> simp[],
     drule_all (SRULE [] pop_range_rounds_boundary) >> simp[],
     drule_all (SRULE [] pop_range_check_boundary) >> simp[],
     drule_all (SRULE [] pop_range_variable_store_boundary) >> simp[],
     gvs[comp_return_def]]
QED
