Theory bodyPtrBytestringBuiltinsArithmeticAllocationTrace
Ancestors bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace exprLowering

Theorem compile_clamp_allocation_trace[simp]:
  !v ty s. allocation_trace s (SND (compile_clamp v ty s))
Proof
  rpt gen_tac >> simp[compile_clamp_def] >> pairarg_tac >> simp[] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem clamp_and_return_allocation_trace[simp]:
  !v ty s. allocation_trace s (SND (clamp_and_return v ty s))
Proof
  rpt gen_tac >> simp[clamp_and_return_def] >>
  irule allocation_trace_ignore_bind >> simp[]
QED

Theorem compile_clamp_basetype_allocation_trace[simp]:
  !v ty s. allocation_trace s (SND (compile_clamp_basetype v ty s))
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[compile_clamp_basetype_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_clamp_basetype_def] >>
  TRY (rename1 `BytesT sz` >> Cases_on `sz` >> simp[compile_clamp_basetype_def]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_safe_add_allocation_trace[simp]:
  !x y ty s. allocation_trace s (SND (compile_safe_add x y ty s))
Proof
  rpt gen_tac >> simp[compile_safe_add_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_safe_sub_allocation_trace[simp]:
  !x y ty s. allocation_trace s (SND (compile_safe_sub x y ty s))
Proof
  rpt gen_tac >> simp[compile_safe_sub_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_mul_overflow_check_allocation_trace[simp]:
  !x y r signed bits s.
    allocation_trace s (SND (compile_mul_overflow_check x y r signed bits s))
Proof
  rpt gen_tac >> simp[compile_mul_overflow_check_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_safe_mul_allocation_trace[simp]:
  !x y ty s. allocation_trace s (SND (compile_safe_mul x y ty s))
Proof
  rpt gen_tac >> simp[compile_safe_mul_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_safe_div_allocation_trace[simp]:
  !x y ty s. allocation_trace s (SND (compile_safe_div x y ty s))
Proof
  rpt gen_tac >> simp[compile_safe_div_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_safe_decimal_div_allocation_trace[simp]:
  !x y divisor ty s.
    allocation_trace s (SND (compile_safe_decimal_div x y divisor ty s))
Proof
  rpt gen_tac >> simp[compile_safe_decimal_div_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_safe_mod_allocation_trace[simp]:
  !x y ty s. allocation_trace s (SND (compile_safe_mod x y ty s))
Proof
  rpt gen_tac >> simp[compile_safe_mod_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED
