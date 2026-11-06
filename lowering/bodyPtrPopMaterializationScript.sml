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

Theorem pop_fresh_var_boundary:
  pop_comp_boundary sa /\ fresh_var sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[fresh_var_def] >> rpt strip_tac >> gvs[pop_comp_boundary_def]
QED

Theorem pop_fresh_label_boundary:
  pop_comp_boundary sa /\ fresh_label suffix sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[fresh_label_def] >> rpt strip_tac >> gvs[pop_comp_boundary_def]
QED

Theorem pop_emit_inst_boundary:
  op <> ASSERT /\ pop_comp_boundary sa /\ emit_inst op args outs sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[pop_comp_boundary_def] >>
  irule pop_boundary_clean_snoc_no_assert >> simp[mk_inst_def]
QED

Theorem pop_word_copy_boundary:
  pop_comp_boundary sa /\
  compile_word_copy_loop src dst n ll sl ctor sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `word_scale ll = 1` >> Cases_on `word_scale sl = 1` >>
  simp[compile_word_copy_loop_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_fresh_label_boundary,
    drule_all pop_fresh_var_boundary,
    drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
    drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
    drule_all pop_ptr_load_boundary, drule_all pop_ptr_store_boundary,
    drule_all pop_comp_boundary_new_block] >> simp[]
QED

Theorem pop_ensure_in_memory_boundary:
  pop_comp_boundary sa /\
  compile_ensure_in_memory ptr_op loc bytes n ctor imm sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `loc` >> Cases_on `n = 1` >>
  simp[compile_ensure_in_memory_def, compile_storage_to_memory_def,
    compile_transient_to_memory_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
    drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
    drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
    drule_all pop_word_copy_boundary, drule_all pop_imm_copy_boundary,
    drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_unwrap_value_boundary:
  pop_comp_boundary sa /\ unwrap_value cenv vv sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `vv` >> simp[unwrap_value_def]
  >- (rpt strip_tac >> drule_all pop_comp_boundary_return >> simp[]) >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >> simp[]
  >- (rpt strip_tac >> drule_all pop_ptr_load_boundary >> simp[]) >>
  Cases_on `p.ptr_location` >> simp[] >> rpt strip_tac >>
  FIRST [drule_all pop_comp_boundary_return,
         drule_all pop_ensure_in_memory_boundary] >> simp[]
QED

Theorem pop_lower_value_boundary:
  (!s v t. pop_comp_boundary s /\ cfn cenv ty e s = (v,t) ==>
            pop_comp_boundary t) /\
  pop_comp_boundary sa /\ lower_value cfn cenv ty e sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[lower_value_def] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >> drule_all pop_unwrap_value_boundary >> simp[]
QED
