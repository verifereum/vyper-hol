Theory bodyPtrBytestringBuiltinsOpcodeArithmetic
Ancestors bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState exprLowering builtinSimple

Theorem no_extcode_clamp:
  !v ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_clamp v ty s))
Proof
  rpt strip_tac >> simp[compile_clamp_def] >> pairarg_tac >> simp[] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_clamp_and_return:
  !v ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (clamp_and_return v ty s))
Proof
  rpt strip_tac >> simp[clamp_and_return_def] >>
  irule no_extcode_ignore_bind >> simp[no_extcode_clamp, no_extcode_fresh_ops]
QED

Theorem no_extcode_clamp_basetype:
  !v ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_clamp_basetype v ty s))
Proof
  rpt strip_tac >> Cases_on `ty` >>
  simp[compile_clamp_basetype_def, no_extcode_fresh_ops] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, no_extcode_fresh_ops] >>
  TRY (rename1 `BytesT sz` >> Cases_on `sz` >>
    simp[compile_clamp_basetype_def, no_extcode_fresh_ops]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_fresh_ops, no_extcode_clamp_and_return])
QED

Theorem no_extcode_safe_add:
  !x y ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_safe_add x y ty s))
Proof
  rpt strip_tac >> simp[compile_safe_add_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_fresh_ops, no_extcode_clamp_and_return])
QED

Theorem no_extcode_safe_sub:
  !x y ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_safe_sub x y ty s))
Proof
  rpt strip_tac >> simp[compile_safe_sub_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_fresh_ops, no_extcode_clamp_and_return])
QED

Theorem no_extcode_mul_overflow_check:
  !x y r signed bits s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_mul_overflow_check x y r signed bits s))
Proof
  rpt strip_tac >> simp[compile_mul_overflow_check_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_safe_mul:
  !x y ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_safe_mul x y ty s))
Proof
  rpt strip_tac >> simp[compile_safe_mul_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
      no_extcode_clamp_and_return, no_extcode_mul_overflow_check])
QED

Theorem no_extcode_safe_div:
  !x y ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_safe_div x y ty s))
Proof
  rpt strip_tac >> simp[compile_safe_div_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_fresh_ops, no_extcode_clamp_and_return])
QED

Theorem no_extcode_safe_decimal_div:
  !x y divisor ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_safe_decimal_div x y divisor ty s))
Proof
  rpt strip_tac >> simp[compile_safe_decimal_div_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_clamp_and_return])
QED

Theorem no_extcode_safe_mod:
  !x y ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_safe_mod x y ty s))
Proof
  rpt strip_tac >> simp[compile_safe_mod_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void])
QED

Theorem no_extcode_safe_pow:
  !x y ty b e s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_safe_pow x y ty b e s))
Proof
  rpt strip_tac >> Cases_on `b` >> Cases_on `e` >> simp[compile_safe_pow_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_inst, no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_fresh_ops, no_extcode_clamp])
QED

Theorem no_extcode_compare:
  !opr x y ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_compare opr x y ty s))
Proof
  rpt strip_tac >> Cases_on `opr` >>
  simp[compile_compare_def, no_extcode_emit_op] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_inst, no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_fresh_ops])
QED

Theorem no_extcode_wrap_truncate:
  !r ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (wrap_truncate r ty s))
Proof
  rpt strip_tac >> simp[wrap_truncate_def] >> rpt IF_CASES_TAC >>
  simp[no_extcode_emit_op, no_extcode_fresh_ops]
QED

Theorem no_extcode_select:
  !c x y s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_select c x y s))
Proof
  rpt strip_tac >> simp[compile_select_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op])
QED

Theorem no_extcode_binop:
  !opr x y ty b e s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_binop opr x y ty b e s))
Proof
  rpt strip_tac >> Cases_on `opr` >> simp[compile_binop_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_inst, no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_fresh_ops, no_extcode_safe_add, no_extcode_safe_sub,
      no_extcode_safe_mul, no_extcode_safe_div, no_extcode_safe_decimal_div,
      no_extcode_safe_mod, no_extcode_compare, no_extcode_safe_pow,
      no_extcode_wrap_truncate, no_extcode_select]) >>
  simp[no_extcode_safe_add, no_extcode_safe_sub, no_extcode_safe_mul,
    no_extcode_safe_div, no_extcode_safe_decimal_div, no_extcode_safe_mod,
    no_extcode_compare, no_extcode_safe_pow, no_extcode_emit_op]
QED
