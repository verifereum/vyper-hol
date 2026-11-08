Theory bodyPtrStructLitOwnershipScalar
Ancestors bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  exprLowering compileEnv builtinSimple

Theorem alloc_run_compile_clamp:
  alloc_run fresh_outputs (compile_clamp val_op ty) (\v s. fresh_outputs s)
Proof
  simp[compile_clamp_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_clamp_and_return:
  alloc_run fresh_outputs (clamp_and_return res ty) (\v s. fresh_outputs s)
Proof
  simp[clamp_and_return_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[alloc_run_compile_clamp] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_safe_add:
  alloc_run fresh_outputs (compile_safe_add x y ty) (\v s. fresh_outputs s)
Proof
  simp[compile_safe_add_def, comp_ignore_bind_def] >>
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_clamp_and_return] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_safe_sub:
  alloc_run fresh_outputs (compile_safe_sub x y ty) (\v s. fresh_outputs s)
Proof
  simp[compile_safe_sub_def, comp_ignore_bind_def] >>
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_clamp_and_return] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_mul_overflow_check:
  alloc_run fresh_outputs (compile_mul_overflow_check x y res signed bits)
    (\v s. fresh_outputs s)
Proof
  simp[compile_mul_overflow_check_def, comp_ignore_bind_def] >>
  Cases_on `signed /\ bits = 256` >> simp[comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_safe_mul:
  alloc_run fresh_outputs (compile_safe_mul x y ty) (\v s. fresh_outputs s)
Proof
  simp[compile_safe_mul_def, comp_ignore_bind_def] >>
  Cases_on `128 < type_bits ty` >> Cases_on `is_decimal_type ty` >>
  Cases_on `type_bits ty < 256` >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_mul_overflow_check] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_clamp_and_return] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_safe_div:
  alloc_run fresh_outputs (compile_safe_div x y ty) (\v s. fresh_outputs s)
Proof
  simp[compile_safe_div_def, comp_ignore_bind_def] >>
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
    SRULE [SF ETA_ss] alloc_run_clamp_and_return] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_safe_decimal_div:
  alloc_run fresh_outputs (compile_safe_decimal_div x y divisor ty)
    (\v s. fresh_outputs s)
Proof
  simp[compile_safe_decimal_div_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_clamp_and_return]
QED

Theorem alloc_run_compile_safe_mod:
  alloc_run fresh_outputs (compile_safe_mod x y ty) (\v s. fresh_outputs s)
Proof
  simp[compile_safe_mod_def, comp_ignore_bind_def] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_wrap_truncate:
  alloc_run fresh_outputs (wrap_truncate res ty) (\v s. fresh_outputs s)
Proof
  simp[wrap_truncate_def] >> Cases_on `type_bits ty < 256` >>
  Cases_on `is_signed_type ty` >> simp[alloc_run_emit_op_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_compare:
  alloc_run fresh_outputs (compile_compare op x y ty) (\v s. fresh_outputs s)
Proof
  Cases_on `op` >> simp[compile_compare_def, comp_ignore_bind_def] >>
  Cases_on `is_uint256 ty` >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
      irule alloc_run_conseq >> irule_at Any alloc_run_emit_inst_fresh >> simp[]) >>
    gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_neg:
  alloc_run fresh_outputs (compile_neg v ty) (\v s. fresh_outputs s)
Proof
  simp[compile_neg_def, comp_ignore_bind_def] >> pairarg_tac >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_invert:
  alloc_run fresh_outputs (compile_invert v ty ce) (\v s. fresh_outputs s)
Proof
  Cases_on `ty` >> simp[compile_invert_def, alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_safe_pow:
  alloc_run fresh_outputs (compile_safe_pow x y ty base_literal exp_literal)
    (\v s. fresh_outputs s)
Proof
  Cases_on `base_literal` >> Cases_on `exp_literal` >>
  simp[compile_safe_pow_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_clamp] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_select:
  alloc_run fresh_outputs (compile_select cond_op then_op else_op)
    (\v s. fresh_outputs s)
Proof
  simp[compile_select_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_binop:
  alloc_run fresh_outputs (compile_binop op x y ty base_literal exp_literal)
    (\v s. fresh_outputs s)
Proof
  Cases_on `op` >> simp[compile_binop_def, comp_ignore_bind_def] >>
  Cases_on `is_decimal_type ty` >> Cases_on `is_signed_type ty` >>
  Cases_on `is_uint256 ty` >>
  simp[alloc_run_compile_safe_add, alloc_run_compile_safe_sub,
    alloc_run_compile_safe_mul, alloc_run_compile_safe_div,
    alloc_run_compile_safe_decimal_div, alloc_run_compile_safe_mod,
    alloc_run_compile_safe_pow, alloc_run_compile_compare,
    alloc_run_emit_op_fresh] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
      irule alloc_run_conseq >> irule_at Any alloc_run_emit_inst_fresh >> simp[]) >>
    gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
    SRULE [SF ETA_ss] alloc_run_wrap_truncate,
    SRULE [SF ETA_ss] alloc_run_compile_select] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_clamp_basetype:
  alloc_run fresh_outputs (compile_clamp_basetype val_op ty)
    (\v s. fresh_outputs s)
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_clamp_basetype_def]) >>
  TRY (rename1 `BytesT sz` >> Cases_on `sz` >> simp[compile_clamp_basetype_def]) >>
  rpt IF_CASES_TAC >> simp[alloc_run_clamp_and_return, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
