Theory bodyPtrPopStatementGuards
Ancestors bodyPtrPopAbiDecodeBoundary bodyPtrPopAbiDecodePrimitiveBoundary
  bodyPtrPopPrecompileBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopMaterialization bodyPtrPopArithmeticBoundary
  bodyPtrPopTypedCopyBoundary bodyPtrPopCopyBoundary bodyPtrPopAllocationBoundary
  context
  stmtLowering exprLowering compileEnv emitHelper list
Libs monadsyntax

Theorem pop_compile_range_bound_checks_boundary:
  pop_comp_boundary sa /\
  compile_range_bound_checks start end_op rounds bound signed sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `signed` >>
  simp[compile_range_bound_checks_def, comp_ignore_bind_def] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_then_boundary >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_boundary >> simp[]
QED

Theorem pop_append_capacity_guard_then_boundary[local]:
  pop_comp_boundary sa /\
  (!s x t. pop_comp_boundary s /\ k s = (x,t) ==> pop_comp_boundary t) /\
  (do valid <- emit_op LT args; ignored <- emit_void ASSERT [valid]; k od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  CONV_TAC (ONCE_DEPTH_CONV (HO_REWR_CONV (GSYM comp_bind_assoc))) >>
  rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[comp_bind_assoc] >>
      drule_at (Pat `comp_bind _ _ _ = _`) pop_staticcall_guard_boundary >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem pop_compile_dynarray_append_boundary:
  load_op <> ASSERT /\ store_op <> ASSERT /\ pop_comp_boundary sa /\
  compile_dynarray_append ce target val ws elem_size elem_ty src_ty
    cap prim load_op store_op sa = (r,sb) ==> pop_comp_boundary sb
Proof
  pure_rewrite_tac[compile_dynarray_append_def, LET_THM, comp_ignore_bind_def] >>
  rpt strip_tac >>
  qabbrev_tac `dst_loc = (case store_op of SSTORE => LocStorage |
    TSTORE => LocTransient | _ => LocMemory)` >>
  Cases_on `prim` >> Cases_on `dst_loc = LocMemory` >> gvs[] >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_append_capacity_guard_then_boundary >>
     disch_then irule >> simp[] >> rpt gen_tac >> strip_tac),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST_PROVE [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
    drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
    drule_all pop_compile_store_memory_boundary >> simp[],
    drule_all pop_word_copy_boundary >> simp[],
    gvs[comp_return_def, AllCaseEqs()]]
QED

Theorem pop_compile_iter_elem_copy_boundary:
  pop_comp_boundary sa /\
  compile_iter_elem_copy ce elem dst mem_size loc slot_addressed target_ty elem_ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `slot_addressed` >> Cases_on `loc` >>
  Cases_on `mem_size <= 32` >> Cases_on `is_word_type target_ty` >>
  simp[compile_iter_elem_copy_def, compile_slot_to_memory_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_all pop_word_copy_boundary >> simp[],
    drule_all pop_ptr_load_boundary >> simp[],
    drule_all pop_compile_store_memory_boundary >> simp[],
    drule_all pop_compile_copy_memory_boundary >> simp[],
    drule_all pop_imm_copy_boundary >> simp[],
    drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
    drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
    gvs[comp_return_def]]
QED
