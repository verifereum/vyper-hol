Theory bodyPtrPopAllocationBoundary
Ancestors bodyPtrPopArithmeticBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract builtinBytes context emitHelper compileEnv venomInst

Theorem pop_emit_void_boundary:
  op <> ASSERT /\ pop_comp_boundary sa /\ emit_void op args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[pop_comp_boundary_def] >>
  irule pop_boundary_clean_snoc_no_assert >> simp[mk_inst_def]
QED

Theorem pop_compile_alloc_buffer_boundary:
  pop_comp_boundary sa /\ compile_alloc_buffer nbytes sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_alloc_buffer_def, Once comp_bind_def] >> pairarg_tac >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_alloc_dynamic_boundary:
  pop_comp_boundary sa /\ compile_alloc_dynamic size_op sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_alloc_dynamic_def] >> rpt strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_fixed_region_with_id_boundary:
  pop_comp_boundary sa /\ compile_fixed_region_with_id nbytes sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  irule pop_boundary_clean_snoc_no_assert >> simp[mk_inst_def]
QED

Theorem pop_compile_slice_out_buf_boundary:
  pop_comp_boundary sa /\ compile_slice_out_buf out_size sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_slice_out_buf_def, Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >> gvs[] >>
  `pop_comp_boundary cs'` by (drule_all pop_compile_alloc_buffer_boundary >> simp[]) >>
  qpat_x_assum `_ cs' = (r,sb)` mp_tac >>
  simp[comp_return_def, comp_bind_def] >> pairarg_tac >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED
