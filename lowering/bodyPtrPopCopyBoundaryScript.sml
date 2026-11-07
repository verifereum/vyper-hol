Theory bodyPtrPopCopyBoundary
Ancestors bodyPtrPopMaterialization bodyPtrPopArithmeticBoundary
  bodyPtrPopAllocationBoundary bodyPtrPopConversionGuardBoundary
  bodyPtrPopCompilerBoundary bodyPtrPopBoundaryContract
  context compileEnv emitHelper venomInst list

Theorem pop_compile_copy_memory_boundary:
  pop_comp_boundary sa /\ compile_copy_memory dst src n sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `n` >> simp[compile_copy_memory_def] >> rpt strip_tac
  >- (drule_all pop_comp_boundary_return >> simp[]) >>
  drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]
QED

Theorem pop_compile_copy_memory_dynamic_boundary:
  pop_comp_boundary sa /\ compile_copy_memory_dynamic dst src len sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_copy_memory_dynamic_def] >> rpt strip_tac >>
  drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]
QED

Theorem pop_compile_with_byte_offset_boundary:
  pop_comp_boundary sa /\ compile_with_byte_offset op off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `off = 0` >> simp[compile_with_byte_offset_def] >> rpt strip_tac
  >- (drule_all pop_comp_boundary_return >> simp[]) >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_bytestring_copy_len_boundary:
  pop_comp_boundary sa /\ compile_bytestring_copy_len src sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_bytestring_copy_len_def, emit_op_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_clean_append_no_assert >> simp[mk_inst_def]
QED

Theorem pop_compile_store_bytestring_boundary:
  pop_comp_boundary sa /\ compile_store_bytestring src dst sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_store_bytestring_def] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_bytestring_copy_len_boundary >> simp[]) >>
  rpt strip_tac >> drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]
QED

Theorem pop_typed_capacity_boundary:
  pop_comp_boundary sa /\
  (do len <- emit_op MLOAD [src];
      too_long <- emit_op GT [len; Lit cap];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok]; return len od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_guard_short_suffix_template >> simp[mk_inst_def] >>
  qexistsl_tac [`GT`,`[MLOAD]`] >> simp[]
QED

Theorem pop_typed_capacity_cont_factor:
  (do len <- emit_op MLOAD [src];
      too_long <- emit_op GT [len; Lit cap];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok]; k len od) =
  comp_bind (do len <- emit_op MLOAD [src];
                 too_long <- emit_op GT [len; Lit cap];
                 ok <- emit_op ISZERO [too_long];
                 emit_void ASSERT [ok]; return len od) k
Proof
  simp[comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem pop_typed_capacity_cont_boundary:
  (!len s v t. pop_comp_boundary s /\ k len s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  (do len <- emit_op MLOAD [src];
      too_long <- emit_op GT [len; Lit cap];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok]; k len od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  once_rewrite_tac[pop_typed_capacity_cont_factor] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_typed_capacity_boundary >> simp[]) >>
  rpt strip_tac >> metis_tac[]
QED
