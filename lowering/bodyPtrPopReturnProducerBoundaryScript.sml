Theory bodyPtrPopReturnProducerBoundary
Ancestors bodyPtrPopTupleBoundary bodyPtrPopAssignmentBoundary
  bodyPtrPopTypedCopyBoundary bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopAllocationBoundary bodyPtrPopAbiEncodeBoundary bodyPtrPopMaterialization
  stmtLowering context compileEnv emitHelper venomInst

Theorem pop_compile_nonreentrant_unlock_boundary:
  pop_comp_boundary sa /\ compile_nonreentrant_unlock key transient view sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `view` >> Cases_on `transient` >>
  simp[compile_nonreentrant_unlock_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]
QED

Theorem pop_compile_internal_return_boundary:
  pop_comp_boundary sa /\
  compile_internal_return ce value rpc nret rt st elems buf sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `0 < nret` >> Cases_on `value` >> Cases_on `buf` >>
  Cases_on `elems = []` >>
  simp[compile_internal_return_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_all pop_compile_load_tuple_elements_boundary >> simp[],
     drule_all pop_compile_store_memory_boundary >> simp[]]
QED

Theorem pop_compile_internal_return_from_env_boundary:
  pop_comp_boundary sa /\
  compile_internal_return_from_env ce ty sty value rpc sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `ce.ce_return_buf` >>
  TRY (rename1 `SOME loc` >> Cases_on `loc`) >>
  simp[compile_internal_return_from_env_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_all pop_compile_internal_return_boundary >> simp[],
     gvs[comp_return_def]]
QED

Theorem pop_compile_external_return_boundary:
  pop_comp_boundary sa /\
  compile_external_return value prim raw info max_size nr key transient view sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `nr` >> Cases_on `value` >> Cases_on `raw` >> Cases_on `prim` >>
  simp[compile_external_return_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
     drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
     drule_all pop_compile_nonreentrant_unlock_boundary >> simp[],
     drule_all pop_compile_alloc_buffer_boundary >> simp[],
     drule_all pop_compile_abi_encode_to_buf_boundary >> simp[],
     gvs[comp_return_def]]
QED
