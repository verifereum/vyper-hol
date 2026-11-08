Theory bodyPtrBytestringBuiltinsHashAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace builtinHashing

Theorem compile_keccak256_word_allocation_trace[simp]:
  !v s. allocation_trace s (SND (compile_keccak256_word v s))
Proof
  rpt gen_tac >> simp[compile_keccak256_word_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_keccak256_bytes_allocation_trace[simp]:
  !v s. allocation_trace s (SND (compile_keccak256_bytes v s))
Proof
  rpt gen_tac >> simp[compile_keccak256_bytes_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_keccak256_bytesm_allocation_trace[simp]:
  !v m s. allocation_trace s (SND (compile_keccak256_bytesm v m s))
Proof
  rpt gen_tac >> simp[compile_keccak256_bytesm_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_sha256_word_allocation_trace[simp]:
  !v s. allocation_trace s (SND (compile_sha256_word v s))
Proof
  rpt gen_tac >> simp[compile_sha256_word_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_sha256_bytes_allocation_trace[simp]:
  !v s. allocation_trace s (SND (compile_sha256_bytes v s))
Proof
  rpt gen_tac >> simp[compile_sha256_bytes_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_sha256_bytesm_allocation_trace[simp]:
  !v m s. allocation_trace s (SND (compile_sha256_bytesm v m s))
Proof
  rpt gen_tac >> simp[compile_sha256_bytesm_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_method_id_hash_allocation_trace[simp]:
  !ty v s. allocation_trace s (SND (compile_method_id_hash ty v s))
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[compile_method_id_hash_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_method_id_hash_def] >>
  rename1 `BytesT sz` >> Cases_on `sz` >> simp[compile_method_id_hash_def]
QED

Theorem compile_method_id_runtime_allocation_trace[simp]:
  !ty v b s. allocation_trace s (SND (compile_method_id_runtime ty v b s))
Proof
  rpt gen_tac >> simp[compile_method_id_runtime_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED
