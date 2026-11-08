Theory bodyPtrBytestringBuiltinsBytesAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace builtinBytes

Theorem compile_assert_slice_bounds_allocation_trace[simp]:
  !a b c s. allocation_trace s (SND (compile_assert_slice_bounds a b c s))
Proof
  rpt gen_tac >> simp[compile_assert_slice_bounds_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_bytestring_src_allocation_trace[simp]:
  !p s. allocation_trace s (SND (compile_bytestring_src p s))
Proof
  rpt gen_tac >> simp[compile_bytestring_src_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_slice_data_allocation_trace[simp]:
  !len p a n sz s. allocation_trace s (SND (compile_slice_data len p a n sz s))
Proof
  rpt gen_tac >> simp[compile_slice_data_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_slice_out_buf_allocation_trace[simp]:
  !sz s. allocation_trace s (SND (compile_slice_out_buf sz s))
Proof
  rpt gen_tac >> simp[compile_slice_out_buf_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_slice_calldata_allocation_trace[simp]:
  !a n sz s. allocation_trace s (SND (compile_slice_calldata a n sz s))
Proof
  rpt gen_tac >> simp[compile_slice_calldata_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, pairarg_tac] >> simp[])
QED

Theorem compile_slice_code_allocation_trace[simp]:
  !a n sz s. allocation_trace s (SND (compile_slice_code a n sz s))
Proof
  rpt gen_tac >> simp[compile_slice_code_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, pairarg_tac] >> simp[])
QED

Theorem compile_slice_extcode_allocation_trace[simp]:
  !addr a n buf data s.
    allocation_trace s (SND (compile_slice_extcode addr a n buf data s))
Proof
  rpt gen_tac >> simp[compile_slice_extcode_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_extract32_load_allocation_trace[simp]:
  !len p a s. allocation_trace s (SND (compile_extract32_load len p a s))
Proof
  rpt gen_tac >> simp[compile_extract32_load_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED
