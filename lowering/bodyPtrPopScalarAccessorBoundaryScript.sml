Theory bodyPtrPopScalarAccessorBoundary
Ancestors bodyPtrPopMaterialization bodyPtrPopArithmeticBoundary
  bodyPtrPopCompilerBoundary exprLowering builtinMisc compileEnv emitHelper

Theorem pop_compile_env_var_boundary:
  pop_comp_boundary sa /\ compile_env_var ev sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `ev` >> simp[compile_env_var_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_invert_boundary:
  pop_comp_boundary sa /\ compile_invert v ty cenv sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `ty` >> simp[compile_invert_def] >> rpt strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_blobhash_boundary:
  pop_comp_boundary sa /\ compile_blobhash n sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_blobhash_def] >> rpt strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_compile_acc_boundary:
  (!s v t. pop_comp_boundary s /\
     cfn cenv (BaseT AddressT) addr_e s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\ compile_acc cfn cenv addr_e acc sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `acc` >> simp[compile_acc_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (dxrule_all pop_lower_value_boundary >> strip_tac) >>
  rpt (dxrule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >>
       simp[] >> disch_then assume_tac) >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]
QED
