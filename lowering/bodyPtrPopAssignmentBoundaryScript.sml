Theory bodyPtrPopAssignmentBoundary
Ancestors bodyPtrPopTypedCopyBoundary bodyPtrPopCopyBoundary
  bodyPtrPopMaterialization bodyPtrPopCompilerBoundary bodyPtrPopAllocationBoundary
  bodyPtrPopArithmeticBoundary stmtLowering context compileEnv emitHelper list

Theorem pop_compile_imm_store_words_boundary:
  !n off sa r sb. pop_comp_boundary sa /\
  compile_imm_store_words imm src dst n off sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct_on `n` >> simp[compile_imm_store_words_def, comp_ignore_bind_def]
  >- (rpt strip_tac >> drule_all pop_comp_boundary_return >> simp[]) >>
  rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_all pop_lit_byte_offset_boundary >> simp[],
    drule_all pop_imm_store_boundary >> simp[],
    drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
    first_x_assum drule_all >> simp[]]
QED

Theorem pop_compile_dynarray_to_storage_boundary:
  pop_comp_boundary sa /\
  compile_dynarray_to_storage src dst ew ems transient sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `transient` >> Cases_on `ew = 1` >>
  simp[compile_dynarray_to_storage_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_all pop_fresh_label_boundary >> simp[],
    drule_all pop_fresh_var_boundary >> simp[],
    drule_all pop_comp_boundary_new_block >> simp[],
    drule_all pop_word_copy_boundary >> simp[],
    drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
    drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
    drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]]
QED

Theorem pop_compile_store_at_loc_boundary:
  pop_comp_boundary sa /\ compile_store_at_loc imm dst val lo sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `lo` >> simp[compile_store_at_loc_def] >> rpt strip_tac
  >- (drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
  Cases_on `x` >> gvs[compile_store_at_loc_def] >>
  FIRST_PROVE [drule_all pop_imm_store_boundary >> simp[],
    drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]]
QED


Theorem pop_compile_assign_value_boundary:
  pop_comp_boundary sa /\
  compile_assign_value ce dst loc val prim src_lo dst_ty src_ty dynarray_info mem_size sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `dynarray_info` >- suspend "none" >>
  rename1 `SOME dims` >> PairCases_on `dims` >> suspend "some"
QED

Resume pop_compile_assign_value_boundary[none]:
  Cases_on `loc` >> Cases_on `prim` >>
  Cases_on `type_memory_bytes ce src_ty <= 32` >> Cases_on `mem_size <= 32` >>
  simp[compile_assign_value_def, compile_memory_to_storage_def,
    compile_memory_to_transient_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >> gvs[] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_all pop_compile_alloc_buffer_boundary >> simp[],
    drule_all pop_compile_copy_memory_boundary >> simp[],
    drule_all pop_compile_store_memory_boundary >> simp[],
    drule_all pop_compile_store_memory_typed_boundary >> simp[],
    drule_all pop_compile_dynarray_to_storage_boundary >> simp[],
    drule_all pop_imm_store_boundary >> simp[],
    drule_all pop_compile_imm_store_words_boundary >> simp[],
    drule_all pop_word_copy_boundary >> simp[],
    drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
    drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
    drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
    gvs[comp_return_def]]
QED

Resume pop_compile_assign_value_boundary[some]:
  Cases_on `loc` >> Cases_on `prim` >>
  Cases_on `type_memory_bytes ce src_ty <= 32` >> Cases_on `mem_size <= 32` >>
  simp[compile_assign_value_def, compile_memory_to_storage_def,
    compile_memory_to_transient_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >> gvs[] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_all pop_compile_alloc_buffer_boundary >> simp[],
    drule_all pop_compile_copy_memory_boundary >> simp[],
    drule_all pop_compile_store_memory_boundary >> simp[],
    drule_all pop_compile_store_memory_typed_boundary >> simp[],
    drule_all pop_compile_dynarray_to_storage_boundary >> simp[],
    drule_all pop_imm_store_boundary >> simp[],
    drule_all pop_compile_imm_store_words_boundary >> simp[],
    drule_all pop_word_copy_boundary >> simp[],
    drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
    drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
    drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
    gvs[comp_return_def]]
QED

Finalise pop_compile_assign_value_boundary
