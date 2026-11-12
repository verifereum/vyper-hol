Theory bodyIntCallCompilerScalar
Ancestors
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit bodyIntCallCompilerInterval
  exprLowering compileEnv builtinSimple builtinMath builtinMisc

Theorem intcall_interval_clamp:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_clamp v ty a))
Proof
  strip_tac >> Cases_on `type_bounds ty` >> simp[compile_clamp_def] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_clamp_return:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (clamp_and_return v ty a))
Proof
  strip_tac >> simp[clamp_and_return_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_clamp, intcall_interval_return]
QED

Theorem intcall_interval_safe_add:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_safe_add x y ty a))
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_add_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_clamp_return, intcall_interval_return])
QED

Theorem intcall_interval_safe_sub:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_safe_sub x y ty a))
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_sub_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_clamp_return, intcall_interval_return])
QED

Theorem intcall_interval_mul_check:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_mul_overflow_check x y res sg bits a))
Proof
  strip_tac >> Cases_on `sg /\ bits = 256` >>
  simp[compile_mul_overflow_check_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_safe_mul:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_safe_mul x y ty a))
Proof
  strip_tac >> Cases_on `type_bits ty > 128` >>
  Cases_on `is_decimal_type ty` >> Cases_on `type_bits ty < 256` >>
  simp[compile_safe_mul_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_mul_check,
            intcall_interval_clamp_return, intcall_interval_return])
QED

Theorem intcall_interval_safe_div:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_safe_div x y ty a))
Proof
  strip_tac >> Cases_on `is_signed_type ty` >>
  Cases_on `type_bits ty = 256` >> Cases_on `type_bits ty < 256` >>
  simp[compile_safe_div_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_clamp_return, intcall_interval_return])
QED

Theorem intcall_interval_safe_decimal_div:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_safe_decimal_div x y dv ty a))
Proof
  strip_tac >> simp[compile_safe_decimal_div_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_clamp_return])
QED

Theorem intcall_interval_safe_mod:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_safe_mod x y ty a))
Proof
  strip_tac >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_safe_pow:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_safe_pow x y ty bl el a))
Proof
  strip_tac >> Cases_on `bl` >> Cases_on `el` >>
  simp[compile_safe_pow_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_clamp, intcall_interval_return])
QED

Theorem intcall_interval_compare:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_compare op x y ty a))
Proof
  strip_tac >> Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, comp_ignore_bind_def, intcall_interval_emit_op] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_inst,
            intcall_interval_return])
QED

Theorem intcall_interval_wrap_truncate:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (wrap_truncate v ty a))
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, intcall_interval_emit_op, intcall_interval_return]
QED

Theorem intcall_interval_select:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_select c x y a))
Proof
  strip_tac >> simp[compile_select_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op])
QED

Theorem intcall_interval_binop:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_binop op x y ty bl el a))
Proof
  strip_tac >> Cases_on `op` >> Cases_on `is_signed_type ty` >>
  Cases_on `is_decimal_type ty` >> Cases_on `is_uint256 ty` >>
  simp[compile_binop_def, comp_ignore_bind_def, intcall_interval_safe_add,
       intcall_interval_safe_sub, intcall_interval_safe_mul,
       intcall_interval_safe_div, intcall_interval_safe_decimal_div,
       intcall_interval_safe_mod, intcall_interval_safe_pow,
       intcall_interval_compare, intcall_interval_emit_op] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_inst,
            intcall_interval_wrap_truncate, intcall_interval_select,
            intcall_interval_return])
QED

Theorem intcall_interval_invert:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_invert v ty cenv a))
Proof
  Cases_on `ty` >> simp[compile_invert_def, intcall_interval_emit_op]
QED

Theorem intcall_interval_neg:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_neg v ty a))
Proof
  strip_tac >> Cases_on `type_bounds ty` >>
  simp[compile_neg_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_abs:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_builtin_abs v a))
Proof
  strip_tac >> simp[compile_builtin_abs_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_select])
QED

Theorem intcall_interval_addmod:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_addmod x y z a))
Proof
  strip_tac >> simp[compile_addmod_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_op, intcall_interval_emit_void]
QED

Theorem intcall_interval_mulmod:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_mulmod x y z a))
Proof
  strip_tac >> simp[compile_mulmod_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_op, intcall_interval_emit_void]
QED

Theorem intcall_interval_pow_mod256:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_pow_mod256 x y a))
Proof
  simp[compile_pow_mod256_def, intcall_interval_emit_op]
QED

Theorem intcall_interval_floor:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_floor v dv a))
Proof
  strip_tac >> simp[compile_floor_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_select])
QED

Theorem intcall_interval_ceil:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_ceil v dv a))
Proof
  strip_tac >> simp[compile_ceil_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_select])
QED

Theorem intcall_interval_wei_int:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_as_wei_value_int v scale sg a))
Proof
  strip_tac >> Cases_on `scale = 1` >> Cases_on `sg` >>
  simp[compile_as_wei_value_int_def, comp_ignore_bind_def, intcall_interval_return] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_wei_decimal:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_as_wei_value_decimal v scale dv a))
Proof
  strip_tac >> Cases_on `scale = 1` >>
  simp[compile_as_wei_value_decimal_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED
