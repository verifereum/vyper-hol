Theory bodyPtrBytestringBuiltinsSimpleAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsOperatorAllocationTrace builtinMath builtinMisc builtinSimple

Theorem compile_addmod_allocation_trace[simp]:
  !a b c s. allocation_trace s (SND (compile_addmod a b c s))
Proof
  rpt gen_tac >> simp[compile_addmod_def] >>
  irule allocation_trace_ignore_bind >> simp[]
QED

Theorem compile_mulmod_allocation_trace[simp]:
  !a b c s. allocation_trace s (SND (compile_mulmod a b c s))
Proof
  rpt gen_tac >> simp[compile_mulmod_def] >>
  irule allocation_trace_ignore_bind >> simp[]
QED

Theorem compile_pow_mod256_allocation_trace[simp]:
  !a b s. allocation_trace s (SND (compile_pow_mod256 a b s))
Proof simp[compile_pow_mod256_def]
QED

Theorem compile_builtin_abs_allocation_trace[simp]:
  !v s. allocation_trace s (SND (compile_builtin_abs v s))
Proof
  rpt gen_tac >> simp[compile_builtin_abs_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_builtin_calldatasize_allocation_trace[simp]:
  !s. allocation_trace s (SND (compile_builtin_calldatasize s))
Proof simp[compile_builtin_calldatasize_def]
QED

Theorem compile_builtin_len_allocation_trace[simp]:
  !ctor imm v loc s. allocation_trace s (SND (compile_builtin_len ctor imm v loc s))
Proof simp[compile_builtin_len_def]
QED

Theorem compile_ecrecover_allocation_trace[simp]:
  !h v r ss s. allocation_trace s (SND (compile_ecrecover h v r ss s))
Proof
  rpt gen_tac >> simp[compile_ecrecover_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_ecadd_points_allocation_trace[simp]:
  !p q s. allocation_trace s (SND (compile_ecadd_points p q s))
Proof
  rpt gen_tac >> simp[compile_ecadd_points_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_ecmul_point_allocation_trace[simp]:
  !p n s. allocation_trace s (SND (compile_ecmul_point p n s))
Proof
  rpt gen_tac >> simp[compile_ecmul_point_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_blockhash_allocation_trace[simp]:
  !n s. allocation_trace s (SND (compile_blockhash n s))
Proof
  rpt gen_tac >> simp[compile_blockhash_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_blobhash_allocation_trace[simp]:
  !n s. allocation_trace s (SND (compile_blobhash n s))
Proof simp[compile_blobhash_def]
QED

Theorem compile_floor_allocation_trace[simp]:
  !v d s. allocation_trace s (SND (compile_floor v d s))
Proof
  rpt gen_tac >> simp[compile_floor_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_ceil_allocation_trace[simp]:
  !v d s. allocation_trace s (SND (compile_ceil v d s))
Proof
  rpt gen_tac >> simp[compile_ceil_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_as_wei_value_int_allocation_trace[simp]:
  !v sc b s. allocation_trace s (SND (compile_as_wei_value_int v sc b s))
Proof
  rpt gen_tac >> simp[compile_as_wei_value_int_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_as_wei_value_decimal_allocation_trace[simp]:
  !v sc d s. allocation_trace s (SND (compile_as_wei_value_decimal v sc d s))
Proof
  rpt gen_tac >> simp[compile_as_wei_value_decimal_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED
