Theory bodyPtrPopStatementSimpleBoundary
Ancestors bodyPtrPopMutualBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopMaterialization
  bodyPtrPopAssignmentBoundary bodyPtrPopStatementControl bodyPtrPopAllocationBoundary
  bodyPtrPopTargetBoundary bodyPtrPopTupleBoundary bodyPtrPopBinopBoundary
  stmtLowering compileEnv exprLowering emitHelper supportedStmts venomInst

Theorem pop_stmt_pass_boundary:
  pop_comp_boundary sa /\ compile_stmt ce lc ty Pass sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_stmt_def, comp_return_def] >> rpt strip_tac >> gvs[]
QED

Theorem pop_stmt_expr_boundary:
  supported_expr tops e /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (Expr e) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >>
  (conj_tac >- (rpt strip_tac >> drule_all pop_compile_supported_boundary >> simp[])) >>
  rpt strip_tac >> gvs[comp_return_def]
QED

Theorem pop_stmt_annassign_boundary:
  supported_expr tops e /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (AnnAssign name vty e) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_all pop_emit_local_alloca_boundary >> simp[],
     drule_all pop_compile_supported_boundary >> simp[],
     (qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >>
      IF_CASES_TAC >> simp[comp_return_def] >> strip_tac >> gvs[] >>
      drule_all pop_unwrap_value_boundary >> simp[]),
     (Cases_on `FLOOKUP ce.ce_vars name` >>
      gvs[] >> TRY (rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> gvs[]) >>
      Cases_on `has_length_word vty /\ is_empty_value_expr e` >> gvs[] >> FIRST_PROVE
        [drule_all pop_compile_assign_value_boundary >> simp[],
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]]),
     gvs[comp_return_def] >> NO_TAC]
QED

Theorem pop_stmt_base_assign_boundary:
  supported_assignment tops bindings (BaseTarget bt) e /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (Assign (BaseTarget bt) e) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  `supported_assignment tops bindings (BaseTarget bt) e ==>
    supported_expr tops e /\
    (supported_target tops bindings bt \/ IS_SOME (supported_target_info tops bindings bt))`
    by (simp[supported_assignment_def] >> rpt strip_tac >>
        gvs[AllCaseEqs()] >> Cases_on `supported_target_info tops bindings bt` >> gvs[]) >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e` >>
  simp[compile_stmt_def, comp_ignore_bind_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_all pop_compile_supported_boundary >> simp[],
     (drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`) pop_compile_target_boundary >>
      disch_then irule >> simp[] >> qexistsl [`bindings`, `tops`] >> simp[]),
     drule_all pop_compile_store_at_loc_boundary >> simp[],
     drule_all pop_unwrap_value_boundary >> simp[],
     (BasicProvers.FULL_CASE_TAC >> gvs[] >> FIRST_PROVE
        [drule_all pop_compile_assign_value_boundary >> simp[],
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]]),
     gvs[comp_return_def] >> NO_TAC]
QED

Theorem pop_stmt_tuple_assign_boundary:
  supported_assignment tops bindings (TupleTarget targets) e /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (Assign (TupleTarget targets) e) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[supported_assignment_def, compile_stmt_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_all pop_compile_supported_boundary >> simp[],
     drule_all pop_unwrap_value_boundary >> simp[],
     drule_all pop_compile_tuple_unpack_boundary >> simp[], gvs[comp_return_def]]
QED

Theorem pop_augassign_continuation_boundary[local]:
  supported_expr tops e /\ pop_comp_boundary sa /\
  (case lo of NONE => emit_void INVALID []
   | SOME loc =>
     do load_opc <- return (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD);
        store_opc <- return (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE);
        cur <- emit_op load_opc [dst];
        rhs <- lower_value compile_expr ce target_ty e;
        res <- compile_binop bop cur rhs target_ty NONE
                 (if bop = Exp then expr_int_literal e else NONE);
        emit_void store_opc [dst; res] od) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `lo`
  >- (simp[] >> rpt strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[Once comp_bind_def, comp_return_def] >>
  simp[Once comp_bind_def, comp_return_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [gvs[comp_return_def] >> NO_TAC,
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
     drule_all pop_compile_binop_boundary >> simp[],
     (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
      disch_then irule >> simp[] >> rpt strip_tac >>
      drule_all pop_compile_supported_boundary >> simp[])]
QED

Theorem pop_stmt_augassign_boundary:
  supported_stmt tops bindings (AugAssign target_ty bt bop e) /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty (AugAssign target_ty bt bop e) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[supported_stmt_def, compile_stmt_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >>
  (conj_tac >-
    FIRST_PROVE
      [(rpt strip_tac >>
        drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`) pop_compile_target_boundary >>
        disch_then irule >> simp[] >> qexistsl [`bindings`, `tops`] >> simp[] >> NO_TAC),
       (rpt strip_tac >> drule_all pop_compile_aug_target_boundary >> simp[])]) >>
  rpt strip_tac >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[Once comp_bind_def, comp_return_def] >>
  simp[Once comp_bind_def, comp_return_def] >> strip_tac >>
  drule_all pop_augassign_continuation_boundary >> simp[]
QED
