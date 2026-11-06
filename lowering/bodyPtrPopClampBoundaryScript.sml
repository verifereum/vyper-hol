Theory bodyPtrPopClampBoundary
Ancestors bodyPtrPopCompilerBoundary bodyPtrPopBoundaryContract
  bodyPtrPopGuardedWindow exprLowering emitHelper compileEnv venomInst list

Theorem pop_boundary_append_no_sub:
  pop_boundary_clean p /\ EVERY (\i. i.inst_opcode <> SUB) t /\
  ~pop_guard4 (p ++ t) ==> pop_boundary_clean (p ++ t)
Proof
  simp[pop_boundary_clean_def] >>
  metis_tac[pop_guarded5_append_no_sub]
QED

Theorem pop_clamp_short_template:
  MAP (\i. i.inst_opcode) t = [op;ISZERO;ASSERT] /\
  op <> SUB /\ op <> ISZERO /\ pop_boundary_clean p ==>
  pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_clamp_signed_template:
  MAP (\i. i.inst_opcode) t = [SLT;ISZERO;SGT;ISZERO;AND;ASSERT] /\
  pop_boundary_clean p ==> pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_compile_clamp_shape:
  compile_clamp v ty sa = (r,sb) ==>
  ?t. sb.cs_current_insts = sa.cs_current_insts ++ t /\
    sb.cs_blocks = sa.cs_blocks /\
    MAP (\i. i.inst_opcode) t =
      (if is_signed_type ty then [SLT;ISZERO;SGT;ISZERO;AND;ASSERT]
       else [GT;ISZERO;ASSERT])
Proof
  Cases_on `type_bounds ty` >> Cases_on `is_signed_type ty` >>
  simp[compile_clamp_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem pop_compile_clamp_boundary:
  pop_comp_boundary sa /\ compile_clamp v ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> drule pop_compile_clamp_shape >> strip_tac >>
  gvs[pop_comp_boundary_def] >> Cases_on `is_signed_type ty` >> gvs[]
  >- (irule pop_clamp_signed_template >> goal_assum drule >> simp[]) >>
  irule pop_clamp_short_template >> goal_assum drule >> simp[]
QED

Theorem pop_clamp_and_return_boundary:
  pop_comp_boundary sa /\ clamp_and_return v ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[clamp_and_return_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def] >> pairarg_tac >> rpt strip_tac >> gvs[] >>
  drule_all pop_compile_clamp_boundary >> simp[]
QED

Theorem pop_single_bound_check_boundary:
  op <> SUB /\ op <> ISZERO /\ pop_comp_boundary sa /\
  (do a <- emit_op op args;
      b <- emit_op ISZERO [a];
      emit_void ASSERT [b];
      return v od) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_clamp_short_template >> simp[mk_inst_def]
QED

Theorem pop_compile_clamp_basetype_boundary:
  pop_comp_boundary sa /\ compile_clamp_basetype v ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `b` >>
  gvs[compile_clamp_basetype_def, comp_return_def]
  >~ [`clamp_and_return v (BaseT (UintT n))`]
  >- (Cases_on `n < 256` >> gvs[comp_return_def] >>
      drule_all pop_clamp_and_return_boundary >> simp[])
  >~ [`clamp_and_return v (BaseT (IntT n))`]
  >- (Cases_on `n < 256` >> gvs[comp_return_def] >>
      drule_all pop_clamp_and_return_boundary >> simp[])
  >~ [`compile_clamp_basetype v (BaseT (BytesT bt))`]
  >- (Cases_on `bt` >> gvs[compile_clamp_basetype_def, comp_return_def] >>
      Cases_on `n < 32` >> gvs[comp_return_def] >>
      drule_at (Pat `_ sa = (_,sb)`) pop_single_bound_check_boundary >> simp[]) >>
  drule_at (Pat `_ sa = (_,sb)`) pop_single_bound_check_boundary >> simp[]
QED
