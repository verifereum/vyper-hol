Theory bodyPtrPopBinopBoundary
Ancestors bodyPtrPopMaterialization bodyPtrPopArithmeticBoundary
  bodyPtrPopDivisionFamilyBoundary bodyPtrPopPowBoundary bodyPtrPopSmallMathBoundary
  bodyPtrPopCompilerBoundary exprLowering compileEnv emitHelper

Theorem pop_compile_compare_boundary:
  pop_comp_boundary sa /\ compile_compare op x y ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_at (Pat `comp_return _ _ = _`) pop_comp_boundary_return] >> simp[]
QED

Theorem pop_wrap_truncate_boundary:
  pop_comp_boundary sa /\ wrap_truncate v ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_binop_boundary:
  pop_comp_boundary sa /\ compile_binop op x y ty bl el sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `op` >> Cases_on `is_decimal_type ty` >>
  Cases_on `is_signed_type ty` >> Cases_on `is_uint256 ty` >>
  simp[compile_binop_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_safe_add_boundary,
         drule_all pop_compile_safe_sub_boundary,
         drule_all pop_compile_safe_mul_boundary,
         drule_all pop_compile_safe_div_boundary,
         drule_all pop_compile_safe_decimal_div_boundary,
         drule_all pop_compile_safe_mod_boundary,
         drule_all pop_compile_safe_pow_boundary,
         drule_all pop_compile_select_boundary,
         drule_all pop_compile_compare_boundary,
         drule_all pop_wrap_truncate_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_at (Pat `comp_return _ _ = _`) pop_comp_boundary_return] >> simp[]
QED
