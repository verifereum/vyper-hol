Theory bodyPtrPopPowBoundary
Ancestors bodyPtrPopArithmeticBoundary bodyPtrPopClampBoundary
  bodyPtrPopCompilerBoundary bodyPtrPopBoundaryContract
  bodyPtrPopGuardedWindow exprLowering emitHelper compileEnv venomInst list

Theorem pop_no_sub_finished_template:
  pop_boundary_clean p /\ EVERY (\i. i.inst_opcode <> SUB) t /\
  t <> [] /\ (LAST t).inst_opcode <> ASSERT ==>
  pop_boundary_clean (p ++ t)
Proof
  Cases_on `t` using SNOC_CASES >> simp[SNOC_APPEND] >> rpt strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule pop_boundary_append_no_sub >> simp[EVERY_APPEND] >>
  pure_rewrite_tac[APPEND_ASSOC] >>
  irule pop_guard4_snoc_no_assert >> simp[]
QED

Theorem pop_pow_base_literal_boundary:
  pop_comp_boundary sa /\ compile_safe_pow x y ty (SOME b) el sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `b = -1 \/ b = 0 \/ b = 1` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_pow_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_pow_exponent_literal_boundary:
  pop_comp_boundary sa /\ compile_safe_pow x y ty NONE (SOME e) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `Num e = 0 \/ Num e = 1` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_pow_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_pow_fallback_boundary:
  pop_comp_boundary sa /\ compile_safe_pow x y ty NONE NONE sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_safe_pow_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  drule_all pop_compile_clamp_boundary >> simp[]
QED

Theorem pop_compile_safe_pow_boundary:
  pop_comp_boundary sa /\ compile_safe_pow x y ty bl el sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `bl`
  >- (Cases_on `el` >> rpt strip_tac
      >- (drule_all pop_pow_fallback_boundary >> simp[]) >>
      drule_all pop_pow_exponent_literal_boundary >> simp[]) >>
  rpt strip_tac >> drule_all pop_pow_base_literal_boundary >> simp[]
QED
