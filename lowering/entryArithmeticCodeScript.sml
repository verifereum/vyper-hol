Theory entryArithmeticCode
Ancestors
  entryCodePredicate entryContextCodePredicate exprLowering

Theorem entry_code_compile_clamp:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_clamp v ty)
Proof
  simp[compile_clamp_def] >> pairarg_tac >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void]
QED

Theorem entry_code_clamp_and_return:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (clamp_and_return v ty)
Proof
  simp[clamp_and_return_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_compile_clamp, entry_code_return]
QED

Theorem entry_code_safe_add:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_safe_add x y ty)
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_add_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_clamp_and_return, entry_code_return]
QED

Theorem entry_code_safe_sub:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_safe_sub x y ty)
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_sub_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_clamp_and_return, entry_code_return]
QED

Theorem entry_code_mul_overflow_check:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_mul_overflow_check x y res signed bits)
Proof
  Cases_on `signed` >> Cases_on `bits = 256` >>
  simp[compile_mul_overflow_check_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_return] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void] >>
  irule entry_code_bind >> reverse conj_tac
  >- (rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_emit_op]) >>
  simp[entry_code_emit_void]
QED

Theorem entry_code_safe_mul:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_safe_mul x y ty)
Proof
  Cases_on `type_bits ty > 128` >> Cases_on `is_decimal_type ty` >>
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty < 256` >>
  simp[compile_safe_mul_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_return, entry_code_mul_overflow_check] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_clamp_and_return, entry_code_return]
QED

Theorem entry_code_safe_div:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_safe_div x y ty)
Proof
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >>
  simp[compile_safe_div_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_clamp_and_return, entry_code_return, entry_code_emit_op]
QED

Theorem entry_code_safe_decimal_div:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_safe_decimal_div x y divisor ty)
Proof
  simp[compile_safe_decimal_div_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_clamp_and_return]
QED

Theorem entry_code_safe_mod:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_safe_mod x y ty)
Proof
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_op]
QED

Theorem entry_code_safe_pow:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_safe_pow x y ty bl el)
Proof
  Cases_on `bl` >> Cases_on `el` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_pow_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void, entry_code_compile_clamp,
            entry_code_return] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return, entry_code_emit_op] >>
  irule entry_code_bind >> reverse conj_tac
  >- (irule entry_code_bind >> simp[entry_code_emit_op]) >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_emit_void, entry_code_emit_op]
QED

Theorem entry_code_compare:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_compare bop x y ty)
Proof
  Cases_on `bop` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, compileEnvTheory.comp_ignore_bind_def,
       entry_code_emit_op] >>
  irule entry_code_bind >>
  simp[entry_code_emit_op, entry_code_emit_inst, entry_code_return]
QED

Theorem entry_code_wrap_truncate:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (wrap_truncate res ty)
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, entry_code_emit_op, entry_code_return]
QED

Theorem entry_code_expr_clamp_basetype:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_clamp_basetype v ty)
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def, entry_code_return] >>
  rename1 `compile_clamp_basetype v (BaseT bt)` >>
  Cases_on `bt` >> simp[compile_clamp_basetype_def, entry_code_return]
  >~ [`compile_clamp_basetype v (BaseT (BytesT bs))`]
  >- (Cases_on `bs` >> simp[compile_clamp_basetype_def, entry_code_return] >>
      IF_CASES_TAC >> simp[entry_code_return, compileEnvTheory.comp_ignore_bind_def] >>
      ntac 3 (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op, entry_code_emit_void] >>
        rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]) >>
  rpt IF_CASES_TAC >> simp[compileEnvTheory.comp_ignore_bind_def,
                           entry_code_clamp_and_return, entry_code_return] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_select[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_select cond_op then_op else_op)
Proof
  simp[builtinSimpleTheory.compile_select_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_binop:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_binop bop x y ty bl el)
Proof
  Cases_on `bop` >> Cases_on `is_signed_type ty` >>
  Cases_on `is_decimal_type ty` >> Cases_on `is_uint256 ty` >>
  simp[compile_binop_def, compileEnvTheory.comp_ignore_bind_def,
       entry_code_safe_add, entry_code_safe_sub, entry_code_safe_mul,
       entry_code_safe_div, entry_code_safe_decimal_div, entry_code_safe_mod,
       entry_code_safe_pow, entry_code_compare, entry_code_emit_op] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_inst] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_wrap_truncate, entry_code_select,
       entry_code_emit_op, entry_code_return]
QED
