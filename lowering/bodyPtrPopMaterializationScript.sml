Theory bodyPtrPopMaterialization
Ancestors bodyPtrPopRootLocationBoundary bodyPtrPopAllocationBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopCompilerBoundary context exprLowering
  compileEnv emitHelper bodyPtrPopBoundaryContract list venomInst

Theorem pop_imm_load_boundary:
  pop_comp_boundary sa /\ compile_imm_load_word ctor imm src sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_clean_append_no_assert >> simp[mk_inst_def]
QED

Theorem pop_ptr_load_boundary:
  pop_comp_boundary sa /\ compile_ptr_load ctor imm loc src sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def] >> rpt strip_tac
  >- (drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[])
  >- (drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[])
  >- (drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[])
  >- (drule_all pop_imm_load_boundary >> simp[]) >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_imm_store_boundary:
  pop_comp_boundary sa /\ compile_imm_store_word imm dst v sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_clean_append_no_assert >> simp[mk_inst_def]
QED

Theorem pop_lit_byte_offset_boundary:
  pop_comp_boundary sa /\ compile_lit_byte_offset op off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `off = 0` >> simp[compile_lit_byte_offset_def]
  >- (rpt strip_tac >> drule_all pop_comp_boundary_return >> simp[]) >>
  Cases_on `op` >> simp[] >> rpt strip_tac
  >- (drule_all pop_comp_boundary_return >> simp[]) >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_imm_copy_boundary:
  !n off sa r sb.
  pop_comp_boundary sa /\
  compile_imm_copy_to_memory ctor imm src dst n off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct_on `n`
  >- (simp[compile_imm_copy_to_memory_def] >> rpt strip_tac >>
      drule_all pop_comp_boundary_return >> simp[]) >>
  simp[compile_imm_copy_to_memory_def, comp_ignore_bind_def] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_lit_byte_offset_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_imm_load_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_lit_byte_offset_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED
