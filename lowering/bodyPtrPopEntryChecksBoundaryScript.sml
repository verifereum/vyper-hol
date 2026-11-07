Theory bodyPtrPopEntryChecksBoundary
Ancestors bodyPtrPopClampBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow moduleLowering
  emitHelper compileEnv venomInst list

Theorem pop_payable_check_boundary:
  pop_comp_boundary sa /\
  (do cv <- emit_op CALLVALUE []; ok <- emit_op ISZERO [cv];
      emit_void ASSERT [ok] od) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_clamp_short_template >> simp[mk_inst_def]
QED

Theorem pop_calldata_size_check_boundary[local]:
  pop_comp_boundary sa /\
  (do cds <- emit_op CALLDATASIZE []; small <- emit_op LT [cds; Lit (n2w n)];
      ok <- emit_op ISZERO [small]; emit_void ASSERT [ok] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_append_no_sub >> simp[mk_inst_def] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_compile_entry_checks_boundary:
  pop_comp_boundary sa /\ compile_entry_checks n payable sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `payable` >> Cases_on `n > 4` >>
  simp[compile_entry_checks_def, comp_ignore_bind_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST_PROVE
    [drule_all pop_payable_check_boundary >> simp[],
     drule_all pop_calldata_size_check_boundary >> simp[],
     gvs[comp_return_def]]
QED
