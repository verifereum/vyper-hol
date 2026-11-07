Theory bodyPtrPopUint2StrBoundary
Ancestors bodyPtrPopMaterialization bodyPtrPopAllocationBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopCompilerBoundary
  builtinStrings compileEnv emitHelper

Theorem pop_compile_uint2str_boundary:
  pop_comp_boundary sa /\ compile_uint2str val_op nd bs sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_uint2str_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_fresh_var_boundary,
         drule_all pop_fresh_label_boundary,
         drule_all pop_comp_boundary_new_block,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED
