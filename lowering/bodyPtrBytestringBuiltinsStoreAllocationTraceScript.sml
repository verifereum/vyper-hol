Theory bodyPtrBytestringBuiltinsStoreAllocationTrace
Ancestors bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace context compileEnv emitHelper

Theorem compile_copy_memory_allocation_trace[simp]:
  !dst src n s. allocation_trace s (SND (compile_copy_memory dst src n s))
Proof
  rpt gen_tac >> Cases_on `n` >> simp[compile_copy_memory_def]
QED

Theorem compile_copy_memory_dynamic_allocation_trace[simp]:
  !dst src len s.
    allocation_trace s (SND (compile_copy_memory_dynamic dst src len s))
Proof
  simp[compile_copy_memory_dynamic_def]
QED

Theorem compile_with_byte_offset_allocation_trace[simp]:
  !base off s. allocation_trace s (SND (compile_with_byte_offset base off s))
Proof
  rpt gen_tac >> Cases_on `off = 0` >> simp[compile_with_byte_offset_def]
QED

Theorem compile_bytestring_copy_len_allocation_trace[simp]:
  !src s. allocation_trace s (SND (compile_bytestring_copy_len src s))
Proof
  rpt gen_tac >> simp[compile_bytestring_copy_len_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_store_bytestring_allocation_trace[simp]:
  !src dst s. allocation_trace s (SND (compile_store_bytestring src dst s))
Proof
  rpt gen_tac >> simp[compile_store_bytestring_def] >>
  irule allocation_trace_bind >> simp[]
QED

Theorem typed_copy_allocation_trace:
  (!cenv dst dt src st s.
    allocation_trace s (SND (compile_store_memory_typed cenv dst dt src st s))) /\
  (!cenv dst src dts sts doff soff s.
    allocation_trace s (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s))) /\
  (!cenv dst dt src st n s.
    allocation_trace s (SND (compile_copy_sarray_typed cenv dst dt src st n s))) /\
  (!cenv dst dt cap src st s.
    allocation_trace s (SND (compile_copy_dynarray_typed cenv dst dt cap src st s))) /\
  (!cenv dst src dfs sfs doff soff s.
    allocation_trace s (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  conj_tac >- suspend "dispatch" >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[] >> simp[Once compile_store_memory_typed_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY (pairarg_tac >> gvs[]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >>
       gvs[allocation_trace_emit_inst_snd])
QED

Resume typed_copy_allocation_trace[dispatch]:
  rpt strip_tac >> simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- (irule allocation_trace_bind >> simp[]) >>
  IF_CASES_TAC >- simp[] >> IF_CASES_TAC >- simp[] >>
  Cases_on `dt` >> simp[] >> Cases_on `st` >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[]
QED

Finalise typed_copy_allocation_trace

Theorem compile_store_memory_typed_allocation_trace[simp]:
  !cenv dst dt src st s.
    allocation_trace s (SND (compile_store_memory_typed cenv dst dt src st s))
Proof
  metis_tac[typed_copy_allocation_trace]
QED

Theorem compile_typed_copy_fields_allocation_trace[simp]:
  !cenv dst src dts sts doff soff s.
    allocation_trace s (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s))
Proof
  metis_tac[typed_copy_allocation_trace]
QED

Theorem compile_copy_sarray_typed_allocation_trace[simp]:
  !cenv dst dt src st n s.
    allocation_trace s (SND (compile_copy_sarray_typed cenv dst dt src st n s))
Proof
  metis_tac[typed_copy_allocation_trace]
QED

Theorem compile_copy_dynarray_typed_allocation_trace[simp]:
  !cenv dst dt cap src st s.
    allocation_trace s (SND (compile_copy_dynarray_typed cenv dst dt cap src st s))
Proof
  metis_tac[typed_copy_allocation_trace]
QED

Theorem compile_struct_typed_copy_allocation_trace[simp]:
  !cenv dst src dfs sfs doff soff s.
    allocation_trace s (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s))
Proof
  metis_tac[typed_copy_allocation_trace]
QED

Theorem compile_store_memory_allocation_trace[simp]:
  !cenv src dst dt st s.
    allocation_trace s (SND (compile_store_memory cenv src dst dt st s))
Proof
  rpt gen_tac >> simp[compile_store_memory_def] >>
  rpt (IF_CASES_TAC >> simp[])
QED
