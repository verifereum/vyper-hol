Theory bodyPtrPopAbiStaticBoundary
Ancestors bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopAllocationBoundary bodyPtrPopMaterialization
  abiEncoder compileEnv emitHelper list

Theorem pop_compile_abi_encode_static_boundary:
  pop_comp_boundary sa /\ compile_abi_encode_static dst src sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_abi_encode_static_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_compile_abi_encode_static_info_boundary:
  pop_comp_boundary sa /\ compile_abi_encode_static_info dst src info sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `info` >> simp[compile_abi_encode_static_info_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_abi_encode_static_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_compile_abi_encode_dyn_static_loop_boundary:
  pop_comp_boundary sa /\
  compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_fresh_label_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_new_block,
         drule_all pop_compile_abi_encode_static_info_boundary] >> simp[]
QED
