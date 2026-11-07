Theory bodyPtrPopTypeWrapperBoundary
Ancestors bodyPtrPopTypeWrapperSupport bodyPtrPopAbiEncodeBoundary
  bodyPtrPopAbiDecodeBoundary bodyPtrPopAllocationBoundary
  bodyPtrPopCopyBoundary bodyPtrPopArithmeticBoundary bodyPtrPopCompilerBoundary
  exprLowering builtinSimple builtinAbi compileEnv emitHelper
Libs monadsyntax

Theorem pop_compile_bytestring_widen_copy_boundary:
  pop_comp_boundary sa /\ compile_bytestring_widen_copy dst v src sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_bytestring_widen_copy_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_compile_copy_memory_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_compile_builtin_empty_complex_boundary:
  pop_comp_boundary sa /\ compile_builtin_empty_complex nbytes bs sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `bs` >> simp[compile_builtin_empty_complex_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_compile_zero_words_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_lower_abi_encode_boundary:
  pop_comp_boundary sa /\ lower_abi_encode ensure mid src info maxlen sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `mid` >> simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_compile_abi_encode_to_buf_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_lower_abi_decode_boundary:
  pop_comp_boundary sa /\ lower_abi_decode data info lo hi nbytes sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `lo = hi` >> simp[lower_abi_decode_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_wrapper_eq_guard_boundary >> simp[] >> NO_TAC),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_wrapper_range_guard_boundary >> simp[] >> NO_TAC),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`) pop_compile_abi_decode_to_buf_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED
