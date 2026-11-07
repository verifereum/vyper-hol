Theory bodyPtrPopStatementControl
Ancestors bodyPtrPopMaterialization bodyPtrPopCompilerBoundary
  stmtLowering compileEnv emitHelper finite_map

Theorem pop_declare_local_boundary:
  pop_comp_boundary sa /\ declare_local ce id ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, comp_bind_def, comp_return_def] >> rpt strip_tac
  >- (pairarg_tac >> gvs[] >> drule_all pop_fresh_var_boundary >> simp[]) >>
  gvs[]
QED

Theorem pop_declare_stmt_local_boundary:
  pop_comp_boundary sa /\ declare_stmt_local ce s sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> drule_all pop_declare_local_boundary >> simp[]
QED

Theorem pop_emit_local_alloca_boundary:
  pop_comp_boundary sa /\ emit_local_alloca ce id sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[emit_local_alloca_def, comp_return_def]
  >- (rpt strip_tac >> gvs[]) >>
  Cases_on `x` >> simp[comp_return_def] >> rpt strip_tac >> gvs[] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME (PtrVar ptr_op nbytes)` >>
  Cases_on `ptr_op` >> gvs[comp_return_def] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]
QED

Theorem pop_emit_jmp_if_not_terminated_boundary:
  pop_comp_boundary sa /\ emit_jmp_if_not_terminated label sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `block_is_terminated sa` >>
  simp[emit_jmp_if_not_terminated_def, comp_get_def, comp_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]
QED
