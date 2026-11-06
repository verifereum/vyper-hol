Theory bodyPtrPopIntClampBoundary
Ancestors bodyPtrPopClampBoundary bodyPtrPopCompilerBoundary
  exprLowering emitHelper compileEnv venomInst list

Theorem pop_compile_int_clamp_shape:
  compile_int_clamp signed bits v sa = (r,sb) ==>
  ?t. sb.cs_current_insts = sa.cs_current_insts ++ t /\
    sb.cs_blocks = sa.cs_blocks /\
    MAP (\i. i.inst_opcode) t =
      (if signed then [SLT;ISZERO;SGT;ISZERO;AND;ASSERT]
       else [GT;ISZERO;ASSERT])
Proof
  Cases_on `signed` >>
  simp[compile_int_clamp_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem pop_compile_int_clamp_boundary:
  pop_comp_boundary sa /\ compile_int_clamp signed bits v sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> drule pop_compile_int_clamp_shape >> strip_tac >>
  gvs[pop_comp_boundary_def] >> Cases_on `signed` >> gvs[]
  >- (irule pop_clamp_signed_template >> goal_assum drule >> simp[]) >>
  irule pop_clamp_short_template >> goal_assum drule >> simp[]
QED
