Theory bodyPtrBytestringBuiltinsAbiEncodeAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace abiEncoder

Theorem compile_abi_int_clamp_allocation_trace[simp]:
  !v bits signed s. allocation_trace s (SND (compile_abi_int_clamp v bits signed s))
Proof
  rpt gen_tac >> Cases_on `signed` >> simp[compile_abi_int_clamp_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_abi_bytes_clamp_allocation_trace[simp]:
  !v m s. allocation_trace s (SND (compile_abi_bytes_clamp v m s))
Proof
  rpt gen_tac >> simp[compile_abi_bytes_clamp_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_abi_clamp_basetype_allocation_trace[simp]:
  !v c s. allocation_trace s (SND (compile_abi_clamp_basetype v c s))
Proof
  rpt gen_tac >> Cases_on `c` >> simp[compile_abi_clamp_basetype_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_abi_zero_pad_allocation_trace[simp]:
  !p n c s. allocation_trace s (SND (compile_abi_zero_pad p n c s))
Proof
  rpt gen_tac >> simp[compile_abi_zero_pad_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_abi_encode_static_allocation_trace[simp]:
  !dst src s. allocation_trace s (SND (compile_abi_encode_static dst src s))
Proof
  rpt gen_tac >> simp[compile_abi_encode_static_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_abi_encode_static_info_allocation_trace[simp]:
  !dst src info s. allocation_trace s (SND (compile_abi_encode_static_info dst src info s))
Proof
  rpt gen_tac >> Cases_on `info` >> simp[compile_abi_encode_static_info_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_abi_encode_dyn_static_loop_allocation_trace[simp]:
  !dst src info az mz len s.
    allocation_trace s (SND (compile_abi_encode_dyn_static_loop dst src info az mz len s))
Proof
  rpt gen_tac >> simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_abi_encode_allocation_trace:
  (!dst cp ci dyn off dp s.
    allocation_trace s (SND (compile_abi_encode_child dst cp ci dyn off dp s))) /\
  (!dst src info s.
    allocation_trace s (SND (compile_abi_encode_to_buf dst src info s))) /\
  (!dst src elems so ho dp s.
    allocation_trace s (SND (compile_abi_encode_complex_elems dst src elems so ho dp s))) /\
  (!dst src info az mz len s.
    allocation_trace s (SND (compile_abi_encode_dyn_loop dst src info az mz len s)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt strip_tac >>
  simp[Once compile_abi_encode_child_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd]) >> gvs[]
QED

Theorem compile_abi_encode_child_allocation_trace[simp]:
  !dst cp ci dyn off dp s.
    allocation_trace s (SND (compile_abi_encode_child dst cp ci dyn off dp s))
Proof
  metis_tac[compile_abi_encode_allocation_trace]
QED

Theorem compile_abi_encode_to_buf_allocation_trace[simp]:
  !dst src info s. allocation_trace s (SND (compile_abi_encode_to_buf dst src info s))
Proof
  metis_tac[compile_abi_encode_allocation_trace]
QED

Theorem compile_abi_encode_complex_elems_allocation_trace[simp]:
  !dst src elems so ho dp s.
    allocation_trace s (SND (compile_abi_encode_complex_elems dst src elems so ho dp s))
Proof
  metis_tac[compile_abi_encode_allocation_trace]
QED

Theorem compile_abi_encode_dyn_loop_allocation_trace[simp]:
  !dst src info az mz len s.
    allocation_trace s (SND (compile_abi_encode_dyn_loop dst src info az mz len s))
Proof
  metis_tac[compile_abi_encode_allocation_trace]
QED
