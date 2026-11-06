Theory bodyPtrPopSmallMathBoundary
Ancestors bodyPtrPopConversionGuardBoundary bodyPtrPopPowBoundary
  bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopBoundaryContract builtinMath builtinSimple
  exprLowering emitHelper compileEnv venomInst list

Theorem pop_compile_addmod_boundary:
  pop_comp_boundary sa /\ compile_addmod a b c sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_addmod_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_compile_mulmod_boundary:
  pop_comp_boundary sa /\ compile_mulmod a b c sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_mulmod_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_compile_select_boundary:
  pop_comp_boundary sa /\ compile_select c a b sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_select_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_clean_append_no_assert >> simp[mk_inst_def]
QED

Theorem pop_neg_guard_boundary[local]:
  pop_comp_boundary sa /\
  (do ok <- emit_op SGT [v; Lit lo]; emit_void ASSERT [ok] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_guard_suffix_template >> simp[mk_inst_def] >>
  qexistsl_tac [`SGT`,`[]`] >> simp[]
QED

Theorem pop_compile_neg_factor[local]:
  compile_neg v ty =
    do (do ok <- emit_op SGT [v; Lit (FST (type_bounds ty))];
           emit_void ASSERT [ok] od);
       emit_op SUB [Lit 0w; v] od
Proof
  Cases_on `type_bounds ty` >>
  simp[compile_neg_def, comp_ignore_bind_def, comp_bind_assoc]
QED

Theorem pop_compile_neg_boundary:
  pop_comp_boundary sa /\ compile_neg v ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[pop_compile_neg_factor, comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> rpt strip_tac >>
  `pop_comp_boundary cs'` by (drule_all pop_neg_guard_boundary >> simp[]) >>
  gvs[] >> drule_at (Pat `_ cs' = (_,sb)`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_abs_guard_boundary[local]:
  pop_comp_boundary sa /\
  (do is_neg <- emit_op SLT [v; Lit 0w];
      is_min <- emit_op EQ [v; nv];
      bad <- emit_op AND [is_neg; is_min];
      ok <- emit_op ISZERO [bad];
      emit_void ASSERT [ok]; return is_neg od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_guard_short_suffix_template >> simp[mk_inst_def] >>
  qexistsl_tac [`AND`,`[SLT;EQ]`] >> simp[]
QED

Theorem pop_compile_builtin_abs_factor[local]:
  compile_builtin_abs v =
    do nv <- emit_op SUB [Lit 0w; v];
       is_neg <- (do is_neg <- emit_op SLT [v; Lit 0w];
                     is_min <- emit_op EQ [v; nv];
                     bad <- emit_op AND [is_neg; is_min];
                     ok <- emit_op ISZERO [bad];
                     emit_void ASSERT [ok]; return is_neg od);
       compile_select is_neg nv v od
Proof
  simp[compile_builtin_abs_def, comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem pop_compile_builtin_abs_boundary:
  pop_comp_boundary sa /\ compile_builtin_abs v sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[pop_compile_builtin_abs_factor, Once comp_bind_def] >>
  pairarg_tac >> rpt strip_tac >> gvs[] >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `_ sa = (_,cs')`) pop_emit_op_boundary >> simp[]) >>
  qpat_x_assum `_ cs' = (r,sb)` mp_tac >>
  simp[Once comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  `pop_comp_boundary cs''` by (drule_all pop_abs_guard_boundary >> simp[]) >>
  drule_all pop_compile_select_boundary >> simp[]
QED
