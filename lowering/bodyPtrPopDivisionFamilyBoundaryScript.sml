Theory bodyPtrPopDivisionFamilyBoundary
Ancestors bodyPtrPopArithmeticBoundary bodyPtrPopDivBoundary
  bodyPtrPopGuardBoundary bodyPtrPopClampBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow bodyPtrPopWindow
  exprLowering emitHelper compileEnv venomInst list

Theorem pop_div_guard_template_boundary:
  MAP (\i. i.inst_opcode) t = [ISZERO;ISZERO;ASSERT;op] /\
  op <> SUB /\ op <> SLOAD /\ op <> TLOAD /\ op <> ASSERT /\
  pop_boundary_clean p ==> pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  rename1 `pop_boundary_clean (p ++ [a;b;c;d])` >>
  `occurs5 pop_guarded5 (p ++ [a;b;c;d] ++ []) <=>
   occurs5 pop_guarded5 p \/ occurs5 pop_guarded5 []` by
    (irule pop_guard_template_separation >> simp[]) >>
  gvs[pop_boundary_clean_def, occurs5_short] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_div_guard_boundary:
  op <> SUB /\ op <> SLOAD /\ op <> TLOAD /\ op <> ASSERT /\
  pop_comp_boundary sa /\
  (do a <- emit_op ISZERO [y];
      b <- emit_op ISZERO [a];
      emit_void ASSERT [b]; emit_op op [x;y] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_div_guard_template_boundary >> simp[mk_inst_def] >>
  qexists_tac `op` >> simp[]
QED

Theorem pop_compile_safe_mod_boundary:
  pop_comp_boundary sa /\ compile_safe_mod x y ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `is_signed_type ty` >> simp[compile_safe_mod_def] >>
  rpt strip_tac >> drule_at (Pat `_ sa = (_,sb)`) pop_div_guard_boundary >> simp[]
QED

Theorem pop_comp_bind_return[local]:
  comp_bind f (\x. comp_return x) = f
Proof
  simp[FUN_EQ_THM, comp_bind_def] >> gen_tac >>
  Cases_on `f x` >> simp[comp_return_def]
QED

Theorem pop_safe_div_factor[local]:
  ~(is_signed_type ty /\ type_bits ty = 256) ==>
  compile_safe_div x y ty =
    do res <- (do a <- emit_op ISZERO [y];
                  b <- emit_op ISZERO [a];
                  emit_void ASSERT [b];
                  emit_op (if is_signed_type ty then SDIV else Div) [x;y] od);
       if is_signed_type ty /\ type_bits ty < 256 then clamp_and_return res ty
       else return res od
Proof
  strip_tac >> Cases_on `is_signed_type ty` >>
  Cases_on `type_bits ty = 256` >> Cases_on `type_bits ty < 256` >>
  gvs[compile_safe_div_def, comp_ignore_bind_def, comp_bind_assoc,
      pop_comp_bind_return]
QED

Theorem pop_compile_safe_div_boundary:
  pop_comp_boundary sa /\ compile_safe_div x y ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `is_signed_type ty /\ type_bits ty = 256`
  >- (rpt strip_tac >> gvs[] >> drule_all pop_signed256_div_boundary >> simp[]) >>
  drule pop_safe_div_factor >> disch_then (qspecl_then [`y`,`x`] SUBST1_TAC) >>
  simp[Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `_ sa = (_,cs')`) pop_div_guard_boundary >>
     Cases_on `is_signed_type ty` >> simp[]) >>
  Cases_on `is_signed_type ty /\ type_bits ty < 256` >>
  gvs[comp_return_def] >> drule_all pop_clamp_and_return_boundary >> simp[]
QED

Theorem pop_safe_decimal_div_factor[local]:
  compile_safe_decimal_div x y divisor ty =
    do x_scaled <- emit_op MUL [x; Lit (n2w divisor)];
       res <- (do a <- emit_op ISZERO [y];
                  b <- emit_op ISZERO [a];
                  emit_void ASSERT [b]; emit_op SDIV [x_scaled;y] od);
       clamp_and_return res ty od
Proof
  simp[compile_safe_decimal_div_def, comp_ignore_bind_def, comp_bind_assoc]
QED

Theorem pop_compile_safe_decimal_div_boundary:
  pop_comp_boundary sa /\ compile_safe_decimal_div x y divisor ty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[pop_safe_decimal_div_factor, Once comp_bind_def] >>
  pairarg_tac >> gvs[] >> simp[Once comp_bind_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  `pop_comp_boundary cs''` by
    (drule_at (Pat `_ cs' = (_,cs'')`) pop_div_guard_boundary >> simp[]) >>
  drule_all pop_clamp_and_return_boundary >> simp[]
QED
