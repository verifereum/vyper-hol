Theory bodyPtrBytestringBuiltinsConversionAllocationTrace
Ancestors bodyPtrBytestringBuiltinsStringAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsStoreAllocationTrace exprLowering builtinSimple

Theorem load_bytestring_as_word_allocation_trace[simp]:
  !v opc s. allocation_trace s (SND (load_bytestring_as_word v opc s))
Proof
  rpt gen_tac >> simp[load_bytestring_as_word_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_int_clamp_allocation_trace[simp]:
  !b n v s. allocation_trace s (SND (compile_int_clamp b n v s))
Proof
  rpt gen_tac >> simp[compile_int_clamp_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_type_convert_allocation_trace[simp]:
  !v conv s. allocation_trace s (SND (compile_type_convert v conv s))
Proof
  rpt gen_tac >> Cases_on `conv` >> simp[compile_type_convert_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC,
              pairarg_tac] >> simp[])
QED

Theorem compile_bytestring_widen_copy_allocation_trace[simp]:
  !dst v src s. allocation_trace s (SND (compile_bytestring_widen_copy dst v src s))
Proof
  rpt gen_tac >> simp[compile_bytestring_widen_copy_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_zero_words_allocation_trace[simp]:
  !p n s. allocation_trace s (SND (compile_zero_words p n s))
Proof
  gen_tac >> Induct >> simp[compile_zero_words_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_builtin_empty_complex_allocation_trace[simp]:
  !sz b s. allocation_trace s (SND (compile_builtin_empty_complex sz b s))
Proof
  rpt gen_tac >> simp[compile_builtin_empty_complex_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED
