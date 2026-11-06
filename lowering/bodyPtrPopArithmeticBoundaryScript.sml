Theory bodyPtrPopArithmeticBoundary
Ancestors bodyPtrPopClampBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow exprLowering
  emitHelper compileEnv venomInst list

Theorem pop_mul_overflow_template:
  MAP (\i. i.inst_opcode) t =
    (if special then [dop;EQ;ISZERO;OR;EQ;NOT;ISZERO;AND;ISZERO;AND;ASSERT]
     else [dop;EQ;ISZERO;OR;ASSERT]) /\
  dop <> SUB /\ pop_boundary_clean p ==>
  pop_boundary_clean (p ++ t)
Proof
  Cases_on `special` >> simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_compile_mul_overflow_shape:
  compile_mul_overflow_check x y res signed bits sa = (r,sb) ==>
  ?t. sb.cs_current_insts = sa.cs_current_insts ++ t /\
    sb.cs_blocks = sa.cs_blocks /\
    MAP (\i. i.inst_opcode) t =
      (if signed /\ bits = 256 then
        [if signed then SDIV else Div;EQ;ISZERO;OR;EQ;NOT;ISZERO;AND;ISZERO;AND;ASSERT]
       else [if signed then SDIV else Div;EQ;ISZERO;OR;ASSERT])
Proof
  Cases_on `signed /\ bits = 256` >>
  simp[compile_mul_overflow_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
  irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem pop_compile_mul_overflow_boundary:
  pop_comp_boundary sa /\
  compile_mul_overflow_check x y res signed bits sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> drule pop_compile_mul_overflow_shape >> strip_tac >>
  gvs[pop_comp_boundary_def] >> irule pop_mul_overflow_template >>
  goal_assum drule >> simp[] >>
  qexistsl_tac [`if signed then SDIV else Div`,`signed /\ bits = 256`] >>
  Cases_on `signed` >> simp[]
QED

Theorem pop_emit_op_boundary:
  op <> ASSERT /\ pop_comp_boundary sa /\ emit_op op args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> rpt strip_tac >>
  gvs[pop_comp_boundary_def] >>
  irule pop_boundary_clean_snoc_no_assert >> simp[mk_inst_def]
QED

Theorem pop_signed_arith_check_boundary:
  cmp <> SUB /\ pop_comp_boundary sa /\
  (do a <- emit_op SLT [y;Lit 0w];
      b <- emit_op cmp [v;x];
      c <- emit_op EQ [a;b];
      emit_void ASSERT [c];
      return v od) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_append_no_sub >> simp[mk_inst_def] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_compile_safe_add_boundary:
  pop_comp_boundary sa /\ compile_safe_add x y ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_safe_add_def, Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  Cases_on `type_bits ty < 256` >> gvs[]
  >- (drule_all pop_clamp_and_return_boundary >> simp[]) >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- (drule_at (Pat `_ cs' = (_,sb)`) pop_signed_arith_check_boundary >> simp[]) >>
  drule_at (Pat `_ cs' = (_,sb)`) pop_single_bound_check_boundary >> simp[]
QED

Theorem pop_compile_safe_sub_boundary:
  pop_comp_boundary sa /\ compile_safe_sub x y ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_safe_sub_def, Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  Cases_on `type_bits ty < 256` >> gvs[]
  >- (drule_all pop_clamp_and_return_boundary >> simp[]) >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- (drule_at (Pat `_ cs' = (_,sb)`) pop_signed_arith_check_boundary >> simp[]) >>
  drule_at (Pat `_ cs' = (_,sb)`) pop_single_bound_check_boundary >> simp[]
QED

Theorem pop_compile_safe_mul_boundary:
  pop_comp_boundary sa /\ compile_safe_mul x y ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_safe_mul_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  `pop_comp_boundary cs''` by
    (Cases_on `128 < type_bits ty` >> gvs[comp_return_def] >>
     drule_all pop_compile_mul_overflow_boundary >> simp[]) >>
  `pop_comp_boundary cs'''` by
    (Cases_on `is_decimal_type ty` >> gvs[comp_return_def] >>
     drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >>
     Cases_on `is_signed_type ty` >> simp[]) >>
  Cases_on `type_bits ty < 256 \/ is_decimal_type ty` >>
  gvs[comp_return_def] >> drule_all pop_clamp_and_return_boundary >> simp[]
QED
