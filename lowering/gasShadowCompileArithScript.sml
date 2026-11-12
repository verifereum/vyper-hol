(* Scalar compiler-operation correspondence. *)
Theory gasShadowCompileArith
Ancestors
  gasShadowCompileContext gasShadowCompileBase gasShadowState exprLowering
  compileEnv emitHelper venomInst builtinSimple

Theorem gas_shadow_compiles_clamp:
  gas_shadow_compiles (compile_clamp v ty) (compile_clamp v ty)
Proof
  Cases_on `type_bounds ty` >> Cases_on `is_signed_type ty` >>
  simp[compile_clamp_def, LET_THM] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_clamp_and_return:
  gas_shadow_compiles (clamp_and_return v ty) (clamp_and_return v ty)
Proof
  simp[clamp_and_return_def, comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_clamp, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_safe_add:
  gas_shadow_compiles (compile_safe_add x y ty) (compile_safe_add x y ty)
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_add_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_clamp_and_return, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_safe_sub:
  gas_shadow_compiles (compile_safe_sub x y ty) (compile_safe_sub x y ty)
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_sub_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_clamp_and_return, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_mul_overflow_check:
  gas_shadow_compiles (compile_mul_overflow_check x y res signed bits)
    (compile_mul_overflow_check x y res signed bits)
Proof
  Cases_on `signed` >> Cases_on `bits = 256` >>
  simp[compile_mul_overflow_check_def, LET_THM, comp_ignore_bind_def] >>
  rpt (pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_safe_mul:
  gas_shadow_compiles (compile_safe_mul x y ty) (compile_safe_mul x y ty)
Proof
  Cases_on `128 < type_bits ty` >> Cases_on `type_bits ty < 256` >>
  Cases_on `is_decimal_type ty` >>
  simp[compile_safe_mul_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_mul_overflow_check,
               gas_shadow_compiles_return] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_clamp_and_return, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_safe_div:
  gas_shadow_compiles (compile_safe_div x y ty) (compile_safe_div x y ty)
Proof
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >>
  simp[compile_safe_div_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_clamp_and_return, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_safe_decimal_div:
  gas_shadow_compiles (compile_safe_decimal_div x y divisor ty)
    (compile_safe_decimal_div x y divisor ty)
Proof
  simp[compile_safe_decimal_div_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_clamp_and_return]
QED

Theorem gas_shadow_compiles_safe_mod:
  gas_shadow_compiles (compile_safe_mod x y ty) (compile_safe_mod x y ty)
Proof
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_wrap_truncate:
  gas_shadow_compiles (wrap_truncate res ty) (wrap_truncate res ty)
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_clamp_basetype:
  gas_shadow_compiles (compile_clamp_basetype v ty) (compile_clamp_basetype v ty)
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def, gas_shadow_compiles_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, gas_shadow_compiles_return] >>
  rpt IF_CASES_TAC >>
  simp[gas_shadow_compiles_clamp_and_return, gas_shadow_compiles_return,
       comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return] >>
  Cases_on `b` >> simp[compile_clamp_basetype_def, gas_shadow_compiles_return] >>
  rpt IF_CASES_TAC >> simp[comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_safe_pow:
  gas_shadow_compiles (compile_safe_pow x y ty base_literal exp_literal)
    (compile_safe_pow x y ty base_literal exp_literal)
Proof
  Cases_on `base_literal` >> Cases_on `exp_literal` >>
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_pow_def, LET_THM, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> asm_rewrite_tac[] >>
  rpt (pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return, gas_shadow_compiles_clamp,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_compare:
  gas_shadow_compiles (compile_compare op x y ty) (compile_compare op x y ty)
Proof
  Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_inst] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_select:
  gas_shadow_compiles (compile_select cond_op then_op else_op)
    (compile_select cond_op then_op else_op)
Proof
  simp[compile_select_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_builtin_len:
  gas_shadow_compiles (compile_builtin_len is_ctor imm ptr_op loc)
    (compile_builtin_len is_ctor imm ptr_op loc)
Proof
  simp[compile_builtin_len_def, gas_shadow_compiles_ptr_load]
QED

Theorem gas_shadow_compiles_builtin_calldatasize:
  gas_shadow_compiles compile_builtin_calldatasize compile_builtin_calldatasize
Proof
  simp[compile_builtin_calldatasize_def]
QED

Theorem gas_shadow_compiles_builtin_empty_prim:
  gas_shadow_compiles compile_builtin_empty_prim compile_builtin_empty_prim
Proof
  simp[compile_builtin_empty_prim_def, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_zero_words:
  !n base. gas_shadow_compiles (compile_zero_words base n) (compile_zero_words base n)
Proof
  Induct >> gen_tac >> once_rewrite_tac[compile_zero_words_def] >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_builtin_empty_complex:
  gas_shadow_compiles (compile_builtin_empty_complex nbytes is_bytestring)
    (compile_builtin_empty_complex nbytes is_bytestring)
Proof
  Cases_on `is_bytestring` >>
  simp[compile_builtin_empty_complex_def, comp_ignore_bind_def, LET_THM] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_zero_words, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_builtin_min:
  gas_shadow_compiles (compile_builtin_min a b unsigned)
    (compile_builtin_min a b unsigned)
Proof
  Cases_on `unsigned` >> simp[compile_builtin_min_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
  simp[gas_shadow_compiles_select]
QED

Theorem gas_shadow_compiles_builtin_max:
  gas_shadow_compiles (compile_builtin_max a b unsigned)
    (compile_builtin_max a b unsigned)
Proof
  Cases_on `unsigned` >> simp[compile_builtin_max_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
  simp[gas_shadow_compiles_select]
QED

Theorem gas_shadow_compiles_builtin_abs:
  gas_shadow_compiles (compile_builtin_abs v) (compile_builtin_abs v)
Proof
  simp[compile_builtin_abs_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_select]
QED

Theorem gas_shadow_compiles_binop:
  gas_shadow_compiles (compile_binop op x y ty base_literal exp_literal)
    (compile_binop op x y ty base_literal exp_literal)
Proof
  Cases_on `op` >> Cases_on `is_decimal_type ty` >>
  Cases_on `is_signed_type ty` >> Cases_on `is_uint256 ty` >>
  simp[compile_binop_def, LET_THM, comp_ignore_bind_def,
       gas_shadow_compiles_safe_add, gas_shadow_compiles_safe_sub,
       gas_shadow_compiles_safe_mul, gas_shadow_compiles_safe_div,
       gas_shadow_compiles_safe_decimal_div, gas_shadow_compiles_safe_mod,
       gas_shadow_compiles_safe_pow, gas_shadow_compiles_compare] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_inst] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_wrap_truncate, gas_shadow_compiles_select,
       gas_shadow_compiles_return]
QED
