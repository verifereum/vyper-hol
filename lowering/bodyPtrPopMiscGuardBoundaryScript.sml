Theory bodyPtrPopMiscGuardBoundary
Ancestors bodyPtrPopConversionGuardBoundary bodyPtrPopPowBoundary
  bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary
  builtinMisc builtinBytes emitHelper compileEnv venomInst list

Theorem pop_compile_as_wei_value_int_boundary:
  pop_comp_boundary sa /\ compile_as_wei_value_int v scale signed sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_guard_suffix_template >> simp[mk_inst_def]
QED

Theorem pop_compile_assert_slice_bounds_boundary:
  pop_comp_boundary sa /\ compile_assert_slice_bounds start len src_len sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_assert_slice_bounds_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_guard_short_suffix_template >> simp[mk_inst_def] >>
  qexistsl_tac [`OR`,`[ADD;LT;GT]`] >> simp[]
QED

Theorem pop_blockhash_suffix_boundary[local]:
  pop_comp_boundary sa /\
  (do too_old <- emit_op SLT [n; lower];
      ok <- emit_op ISZERO [too_old]; emit_void ASSERT [ok];
      in_range <- emit_op LT [n; current]; emit_void ASSERT [in_range];
      emit_op BLOCKHASH [n] od) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_compile_blockhash_boundary:
  pop_comp_boundary sa /\ compile_blockhash n sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_blockhash_def, Once comp_bind_def] >>
  pairarg_tac >> rpt strip_tac >> gvs[] >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `_ sa = (_,cs')`) pop_emit_op_boundary >> simp[]) >>
  qpat_x_assum `_ cs' = (r,sb)` mp_tac >>
  simp[Once comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  `pop_comp_boundary cs''` by
    (drule_at (Pat `_ cs' = (_,cs'')`) pop_emit_op_boundary >> simp[]) >>
  drule_all pop_blockhash_suffix_boundary >> simp[]
QED
