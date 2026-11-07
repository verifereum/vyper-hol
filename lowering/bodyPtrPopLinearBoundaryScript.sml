Theory bodyPtrPopLinearBoundary
Ancestors moduleLowering bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopMaterialization compileEnv list

Theorem pop_selector_checks_boundary:
  !sels op sa r sb.
    pop_comp_boundary sa /\ compile_selector_checks op sels sa = (r,sb) ==>
    pop_comp_boundary sb
Proof
  Induct >> simp[compile_selector_checks_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_selector_checks_def, comp_ignore_bind_def] >> strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [first_x_assum drule_all >> simp[],
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_all pop_fresh_label_boundary >> simp[],
     drule_all pop_comp_boundary_new_block >> simp[]]
QED

Theorem pop_selector_dispatch_linear_boundary:
  pop_comp_boundary sa /\ compile_selector_dispatch_linear sels fallback sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_selector_dispatch_linear_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_all pop_selector_checks_boundary >> simp[],
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_all pop_fresh_label_boundary >> simp[],
     drule_all pop_comp_boundary_new_block >> simp[]]
QED
