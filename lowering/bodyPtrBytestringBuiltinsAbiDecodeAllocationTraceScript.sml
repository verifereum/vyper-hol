Theory bodyPtrBytestringBuiltinsAbiDecodeAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsAbiEncodeAllocationTrace abiEncoder

Theorem compile_get_element_ptr_allocation_trace[simp]:
  !p off s. allocation_trace s (SND (compile_get_element_ptr p off s))
Proof
  simp[compile_get_element_ptr_def]
QED

Theorem compile_get_dynarray_elem_ptr_allocation_trace[simp]:
  !p idx sz s. allocation_trace s (SND (compile_get_dynarray_elem_ptr p idx sz s))
Proof
  rpt gen_tac >> simp[compile_get_dynarray_elem_ptr_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_getelemptr_abi_allocation_trace[simp]:
  !p dyn off opc hi s. allocation_trace s (SND (compile_getelemptr_abi p dyn off opc hi s))
Proof
  rpt gen_tac >> simp[compile_getelemptr_abi_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_abi_decode_dyn_elem_ptr_allocation_trace[simp]:
  !opc elem src hi sz s.
    allocation_trace s (SND (compile_abi_decode_dyn_elem_ptr opc elem src hi sz s))
Proof
  rpt gen_tac >> simp[compile_abi_decode_dyn_elem_ptr_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_abi_decode_static_allocation_trace[simp]:
  !src dst opc clamp s.
    (!v st. allocation_trace st (SND (clamp v st))) ==>
    allocation_trace s (SND (compile_abi_decode_static src dst opc clamp s))
Proof
  rpt strip_tac >> simp[compile_abi_decode_static_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_abi_decode_allocation_trace:
  (!dst src opc hi info s.
    allocation_trace s (SND (compile_abi_decode_to_buf dst src opc hi info s))) /\
  (!dst src opc hi elems ao vo s.
    allocation_trace s (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo s))) /\
  (!dst src opc hi info az mz ip cnt s.
    allocation_trace s (SND (compile_abi_decode_dyn_loop dst src opc hi info az mz ip cnt s)))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd]) >>
  gvs[] >> Cases_on `opc` >> simp[]
QED

Theorem compile_abi_decode_to_buf_allocation_trace[simp]:
  !dst src opc hi info s.
    allocation_trace s (SND (compile_abi_decode_to_buf dst src opc hi info s))
Proof
  metis_tac[compile_abi_decode_allocation_trace]
QED

Theorem compile_abi_decode_complex_elems_allocation_trace[simp]:
  !dst src opc hi elems ao vo s.
    allocation_trace s (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo s))
Proof
  metis_tac[compile_abi_decode_allocation_trace]
QED

Theorem compile_abi_decode_dyn_loop_allocation_trace[simp]:
  !dst src opc hi info az mz ip cnt s.
    allocation_trace s (SND (compile_abi_decode_dyn_loop dst src opc hi info az mz ip cnt s))
Proof
  metis_tac[compile_abi_decode_allocation_trace]
QED
