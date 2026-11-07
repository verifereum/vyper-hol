Theory bodyPtrPopTypeWrapperSupport
Ancestors bodyPtrPopAllocationBoundary bodyPtrPopCopyBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopAbiDecodePrimitiveBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow bodyPtrPopClampBoundary
  builtinSimple compileEnv emitHelper venomInst list
Libs monadsyntax

Theorem pop_compile_zero_words_boundary:
  !n base sa r sb. pop_comp_boundary sa /\
  compile_zero_words base n sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct >> simp[compile_zero_words_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [first_x_assum drule_all,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_abi_wrapper_guard_template:
  MAP (\i. i.inst_opcode) t = [EQ;ASSERT] \/
  MAP (\i. i.inst_opcode) t = [LT;ISZERO;GT;ISZERO;AND;ASSERT] ==>
  pop_boundary_clean p ==> pop_boundary_clean (p ++ t)
Proof
  strip_tac >> gvs[MAP_EQ_CONS] >> rpt strip_tac >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_abi_wrapper_eq_guard_boundary:
  pop_comp_boundary sa /\
  (do valid <- emit_op EQ args; emit_void ASSERT [valid] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_abi_wrapper_guard_template >> simp[mk_inst_def]
QED

Theorem pop_abi_wrapper_range_guard_boundary:
  pop_comp_boundary sa /\
  (do lt <- emit_op LT [v; lo]; ge <- emit_op ISZERO [lt];
      gt <- emit_op GT [v; hi]; le <- emit_op ISZERO [gt];
      valid <- emit_op AND [ge; le]; emit_void ASSERT [valid] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_abi_wrapper_guard_template >> simp[mk_inst_def]
QED
