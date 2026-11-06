Theory bodyPtrPopCalldataSliceBoundary
Ancestors bodyPtrPopAllocationBoundary bodyPtrPopMiscGuardBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopCompilerBoundary builtinBytes compileEnv

Theorem pop_compile_slice_calldata_boundary:
  pop_comp_boundary sa /\
  compile_slice_calldata start_op length_op out_size sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_slice_calldata_def, comp_ignore_bind_def] >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_slice_out_buf_boundary >> simp[]) >>
  qx_gen_tac `bufpair` >> Cases_on `bufpair` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_assert_slice_bounds_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
  rpt strip_tac >> drule_all pop_comp_boundary_return >> simp[]
QED
