Theory gasShadowCompileBuiltinScalar
Ancestors
  gasShadowCompileArith gasShadowCompileContext gasShadowState
  compileEnv builtinMath builtinMisc

Theorem gas_shadow_compiles_addmod:
  gas_shadow_compiles (compile_addmod a b c) (compile_addmod a b c)
Proof
  simp[compile_addmod_def, comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_mulmod:
  gas_shadow_compiles (compile_mulmod a b c) (compile_mulmod a b c)
Proof
  simp[compile_mulmod_def, comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_pow_mod256:
  gas_shadow_compiles (compile_pow_mod256 base_op exp_op) (compile_pow_mod256 base_op exp_op)
Proof
  simp[compile_pow_mod256_def]
QED

Theorem gas_shadow_compiles_blobhash:
  gas_shadow_compiles (compile_blobhash n_op) (compile_blobhash n_op)
Proof
  simp[compile_blobhash_def]
QED

Theorem gas_shadow_compiles_blockhash:
  gas_shadow_compiles (compile_blockhash n_op) (compile_blockhash n_op)
Proof
  simp[compile_blockhash_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_floor:
  gas_shadow_compiles (compile_floor val_op divisor) (compile_floor val_op divisor)
Proof
  simp[compile_floor_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_select] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_ceil:
  gas_shadow_compiles (compile_ceil val_op divisor) (compile_ceil val_op divisor)
Proof
  simp[compile_ceil_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_select] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_ecrecover:
  gas_shadow_compiles (compile_ecrecover hash_op v_op r_op s_op)
    (compile_ecrecover hash_op v_op r_op s_op)
Proof
  simp[compile_ecrecover_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_ecadd_points:
  gas_shadow_compiles (compile_ecadd_points p1 p2) (compile_ecadd_points p1 p2)
Proof
  simp[compile_ecadd_points_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_ecmul_point:
  gas_shadow_compiles (compile_ecmul_point p scalar) (compile_ecmul_point p scalar)
Proof
  simp[compile_ecmul_point_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_as_wei_value_int:
  gas_shadow_compiles (compile_as_wei_value_int val_op scale is_signed)
    (compile_as_wei_value_int val_op scale is_signed)
Proof
  Cases_on `scale = 1` >> Cases_on `is_signed` >>
  simp[compile_as_wei_value_int_def, comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return, gas_shadow_compiles_bind,
               gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_as_wei_value_decimal:
  gas_shadow_compiles (compile_as_wei_value_decimal val_op scale dec_scale)
    (compile_as_wei_value_decimal val_op scale dec_scale)
Proof
  Cases_on `scale = 1` >>
  simp[compile_as_wei_value_decimal_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >> simp[]
QED
